-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapA15_truncatedTaylorHamiltonianSimulation
-- name    : QAlgorithms.Papers.RoadmapA15.truncatedTaylorHamiltonianSimulation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:32:51.99343+00:00
-- url     : https://prove2.me/theorems/8559cc8a-cca5-4f82-bcce-532836f24dbb
-- title:
--   Truncated-Taylor Hamiltonian simulation with logarithmic precision dependence
-- statement:
--   Let $D,L\ge1$, let $\alpha_1,\ldots,\alpha_L>0$ be known coefficients, and let $t>0$ and $0<\epsilon<1$. For any unitary matrices $H_1,\ldots,H_L$ on a $D$-dimensional system whose sum $H=\sum_{\ell=1}^L\alpha_\ell H_\ell$ is Hermitian, count coherent signed controlled selection $|b,\ell,\psi\rangle\mapsto|b,\ell\rangle(-iH_\ell)^b|\psi\rangle$ and its inverse as the access operations. Set $T=t\sum_\ell\alpha_\ell$, $r=\lceil T/\ln2\rceil$, and $n=\lceil\log_2D\rceil$.
--
--   There are absolute constants $C>0$, $c\ge1$, and $q_0>\exp(\exp(1))$, chosen before all instance data, for which the following holds. Choose the least nonnegative truncation order $K$ satisfying $\sum_{k=K+1}^{\infty}(\ln2)^k/k!\le\epsilon/(cr)$. From $D,L,\alpha,t,\epsilon$ alone one can construct the paper's segmented Taylor simulator, before choosing the term oracle or the input state. The simulator uses $r-1$ segments of duration $\ln2/\sum_\ell\alpha_\ell$ and the remaining positive duration as its final segment. Each segment uses the Taylor LCU, the normalization ancilla, and robust oblivious amplification $-WRW^\dagger RW$, with fresh zero ancillas that are subsequently discarded.
--
--   If $J$ is the standard isometric embedding of the $D$-dimensional system into $n$ qubits, $\mathcal S$ denotes the implemented unconditional channel, and $\psi$ is any unit vector, then
--   $$
--   \left\|\mathcal S(J|\psi\rangle\langle\psi|J^\dagger)
--   -J e^{-iHt}|\psi\rangle\langle\psi|e^{iHt}J^\dagger\right\|_1\le\epsilon.
--   $$
--   Every segment's truncated operator differs from its exact evolution by at most $\epsilon/(cr)$ in spectral norm. The same construction also approximates the padded Hamiltonian on every normalized state of the full qubit register. The number of signed-selector calls is at most $Cr(K+1)$; the number of other elementary gates is at most $CLr(K+1)$; and peak ancillary qubits, treating the selector as the primitive access operation, are at most $C(1+\lceil\log_2L\rceil)(K+1)$.
--
--   For $T\ge1$ and $T/\epsilon\ge q_0$, the order and counted access cost satisfy
--   $$
--   K\le C\frac{\log(T/\epsilon)}{\log\log(T/\epsilon)},\qquad
--   Q\le CT\frac{\log(T/\epsilon)}{\log\log(T/\epsilon)}.
--   $$
--   If a signed-selector implementation has $g$ elementary gates and $w$ clean workspace qubits, there are elementary segment circuits implementing the same simulator, returning that workspace to zero, with total gate count at most $C(L+g)r(K+1)$. In the special case in which the padded terms are tensor products of single-qubit Pauli matrices, such circuits exist with total gate count at most $CL(n+1+\lceil\log_2L\rceil)r(K+1)$ and peak ancillary qubits at most $C(1+\lceil\log_2L\rceil)(K+1)$.
--
--   This gives the paper's time-independent simulation cost without requiring commuting, self-inverse, Hermitian individual terms or a bound on $\|H\|$.
--
--   **Formalization Note** The paper does not name the reduced-state norm. Trace norm without the factor $1/2$ is used to make its discard-ancillas and error-accumulation argument precise. Eq. (10)'s failure coefficient, Eq. (16)'s partial trace of a ket, and the printed order-register amplitude are corrected as recorded in the audit. Arbitrary one- and two-qubit gates are used, with exact rotations and inverses; finite-gate-set synthesis overhead is outside the claim.
-- source:
--   Simulating Hamiltonian dynamics with a truncated Taylor series, arXiv:1412.4687v1, Unnumbered time-independent simulation bound; construction pp.3–4, Eqs. (18)–(24), PDF p. 2. https://arxiv.org/abs/1412.4687v1 . PDF SHA-256: 48466bb2bf16df36b24122d38e17446e7fa8d3fb78ddeb2bb12c499a3381cc0a.

import Definitions.Def_QAlgorithms_Defs_TaylorSimulationPrograms
import Definitions.Def_QAlgorithms_Papers_RoadmapA15_Model
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms.Papers.RoadmapA15

open QAlgorithms TaylorSimulation


/-- Berry, Childs, Cleve, Kothari and Somma, arXiv:1412.4687v1, unnumbered
time-independent simulation bound (PDF p.2), with construction and resource accounting
on pp.3–4, Eqs. (18)–(24). The simulator is chosen from public decomposition coefficients,
dimension, time and precision before the term oracle and the input state. Its output includes
all ancillary outcomes and is compared in trace norm, without a factor of one half.

Source corrections: Eq. (10)'s normalized failure coefficient must depend on the norm of the
nonunitary approximant; Eq. (11)'s exact block identity is used instead. Eq. (16)'s partial
trace of a ket is replaced by the unconditional reduced density operator. The order-register
preparation uses the segment coefficient mass, rather than the printed physical time t.
Trace norm is the interpretation of the unspecified reduced-state norm. The additive 1 in
the ancillary and Pauli gate bounds retains the unary register and scalar/one-term cases. -/
theorem truncatedTaylorHamiltonianSimulation :
    ∃ C c threshold : ℝ, 0 < C ∧ 1 ≤ c ∧ Real.exp (Real.exp 1) < threshold ∧
    ∀ (D L : ℕ), 0 < D → 0 < L →
    ∀ alpha : Fin L → ℝ, (∀ j, 0 < alpha j) →
    ∀ t eps : ℝ, 0 < t → 0 < eps → eps < 1 →
    let mass := ∑ j, alpha j
    let T := mass * t
    let r : ℕ := ⌈T / Real.log 2⌉₊
    ∃ positive : 0 < eps / (c * (r : ℝ)),
    let K := orderForPrecision (eps / (c * (r : ℝ))) positive
    ∃ P : SegmentedProgram (Nat.clog 2 D) L K,
      P.alpha = alpha ∧ P.time = t ∧ IsSourceCompilation P ∧
      0 < r ∧ P.durations.length = r ∧
      factorialTail K ≤ eps / (c * (r : ℝ)) ∧
      (1 + P.labelBits : ℝ) ≤ C * (1 + Nat.clog 2 L) * (K + 1) ∧
      (P.queryCount : ℝ) ≤ C * r * (K + 1) ∧
      (P.gateCount : ℝ) ≤ C * L * r * (K + 1) ∧
      ((1 ≤ T ∧ threshold ≤ T / eps) →
        (K : ℝ) ≤ C * Real.log (T / eps) / Real.log (Real.log (T / eps)) ∧
        (P.queryCount : ℝ) ≤
          C * T * Real.log (T / eps) / Real.log (Real.log (T / eps))) ∧
      ∀ H : Fin L → Matrix.unitaryGroup (Fin D) ℂ,
      (∑ j, (alpha j : ℂ) • (H j : Matrix (Fin D) (Fin D) ℂ)).IsHermitian →
      ∃ padded : Fin L → Matrix.unitaryGroup (Qubits (Nat.clog 2 D)) ℂ,
        (∀ j, (padded j : Matrix (Qubits (Nat.clog 2 D)) (Qubits (Nat.clog 2 D)) ℂ) =
          extendEncodedUnitary (finiteRegisterEmbedding D) (H j : Matrix (Fin D) (Fin D) ℂ)) ∧
        IsAccurate P padded eps ∧
        (∀ dt ∈ P.durations,
          specNorm (truncatedOperator
            (∑ j, (alpha j : ℂ) • (padded j : Matrix (Qubits (Nat.clog 2 D)) (Qubits (Nat.clog 2 D)) ℂ)) dt K -
            NormedSpace.exp (-(Complex.I * (dt : ℂ)) •
              ∑ j, (alpha j : ℂ) • (padded j : Matrix (Qubits (Nat.clog 2 D)) (Qubits (Nat.clog 2 D)) ℂ))) ≤
            eps / (c * (r : ℝ))) ∧
        (∀ psi : EuclideanSpace ℂ (Fin D), IsState psi →
          traceNorm (P.output padded
              (finiteRegisterEmbedding D * pureDensity psi * (finiteRegisterEmbedding D)ᴴ) -
            finiteRegisterEmbedding D *
              conjSuperop (NormedSpace.exp (-(Complex.I * (t : ℂ)) •
                ∑ j, (alpha j : ℂ) • (H j : Matrix (Fin D) (Fin D) ℂ))) (pureDensity psi) *
              (finiteRegisterEmbedding D)ᴴ) ≤ eps) ∧
        (∀ (w : ℕ)
            (selector : Circuit oneTwoQubitGateSet
              (1 + Nat.clog 2 L + Nat.clog 2 D + w)),
          ImplementsWithCleanAncillas selector.unitary (signedOracle padded) →
          ∃ circuits : ℝ → Circuit oneTwoQubitGateSet (1 + (P.labelBits + Nat.clog 2 D) + w),
            CompilesSegments P padded w circuits ∧
            ((P.durations.map fun dt => (circuits dt).size).sum : ℝ) ≤
              C * (L + selector.size) * r * (K + 1)) ∧
        ((∃ ops : Fin L → Fin (Nat.clog 2 D) → Stabilizer.Pauli,
            ∀ j, (padded j : Matrix (Qubits (Nat.clog 2 D)) (Qubits (Nat.clog 2 D)) ℂ) = pauliOps (ops j)) →
          ∃ w : ℕ,
          ∃ circuits : ℝ → Circuit oneTwoQubitGateSet (1 + (P.labelBits + Nat.clog 2 D) + w),
            CompilesSegments P padded w circuits ∧
            (1 + P.labelBits + w : ℝ) ≤ C * (1 + Nat.clog 2 L) * (K + 1) ∧
            ((P.durations.map fun dt => (circuits dt).size).sum : ℝ) ≤
              C * L * (Nat.clog 2 D + 1 + Nat.clog 2 L) * r * (K + 1)) := by sorry

end QAlgorithms.Papers.RoadmapA15
