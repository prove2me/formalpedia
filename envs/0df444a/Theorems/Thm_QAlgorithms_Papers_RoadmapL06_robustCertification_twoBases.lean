-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapL06_robustCertification_twoBases
-- name    : QAlgorithms.Papers.RoadmapL06.robustCertification_twoBases
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:24:37.978431+00:00
-- url     : https://prove2.me/theorems/78509d32-0540-4b2e-80bf-7ab1615f9421
-- title:
--   Robust certification in two bases with one logarithmic-qubit measurement
-- statement:
--   There is a single efficient oracle procedure for certifying a pure target state using one copy of an arbitrary mixed lab state. The classical oracle returns the exact amplitudes of the target in the computational basis and in the full-register Hadamard basis, as in Definition 1 of the paper.
--
--   More precisely, there exist a polynomial resource bound $p$, a constant $C>0$, a threshold $n_0\ge1$, a nonnegative sequence $\eta_n\to0$, and measurable sets $G_n$ of normalized $n$-qubit target states such that, for all $n\ge n_0$,
--
--   $$
--   \Pr_{\psi\sim\mathrm{Haar}_n}[\psi\notin G_n]\le C2^{-n}.
--   $$
--
--   For every $\psi\in G_n$ and every density matrix $\rho$ on the same $n$ qubits, write $F(\psi,\rho)=\langle\psi|\rho|\psi\rangle$. The procedure satisfies
--
--   $$
--   \Pr[\mathrm{accept}]\ge F(\psi,\rho),\qquad
--   \Pr[\mathrm{reject}]\ge\frac{1-F(\psi,\rho)}{2}-\eta_n.
--   $$
--
--   It flips one fair classical bit and measures the first $r=n-k$ qubits either all in the $Z$ basis or all in the $X$ basis, where $k=\min\{n,\lceil2\log_2(\max\{2,n\})\rceil\}$. Given the observed prefix, it reads the $2^k$ oracle amplitudes for that prefix, computes the conditional target, and performs one projector/complement measurement on the fixed suffix of $k$ qubits. In the $X$ branch, the full-Hadamard oracle fiber is transformed by $H^{\otimes k}$ to obtain the physical conditional target. A zero target fiber is always rejected. The executed oracle calls, scalar instructions, and suffix circuit gates are bounded by $p(n)$, uniformly over normalized targets and every branch; the compiled accepting effect is the conditional target projector.
--
--   The same good set and error sequence apply simultaneously to all lab density matrices. This provides the paper's constant robustness with only one measurement involving logarithmically many qubits.
--
--   **Formalization Note** The suffix rounding fixes the proof's choice $\gamma=1$. Efficiency is relative to exact complex-answer classical oracle access and ideal scalar operations, with arbitrary one- and two-qubit unitaries for exact synthesis. No finite-precision or oracle-simulation cost is claimed. The Lean statement uses the concrete frozen conditional measurement program and its execution-derived resource counts, and gives the additive soundness of Theorem 1.
-- source:
--   The Power of Two Bases: Robust and copy-optimal certification of nearly all quantum states with few-qubit measurements, arXiv:2602.11616v1, Theorem 1, PDF p. 3. https://arxiv.org/abs/2602.11616v1 . PDF SHA-256: 189de75ce585a487dfb393a1aae21f65f1f9008d170a29c04dc3319f9e6a2eab.

import Definitions.Def_QAlgorithms_Defs_TwoBasisCertification
set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace QAlgorithms.Papers.RoadmapL06

open QAlgorithms.TwoBasisCertification

/-- Theorem 1 of Coladangelo, Li, Slote and Wu, *The Power of Two Bases*
(arXiv:2602.11616v1), PDF p.3; oracle model: Definition 1, p.7; test: pp.8–9.

One fixed classical amplitude-oracle program compiles the conditional suffix projector.
The fair choice of a common Z/X prefix basis, one lab copy, and one suffix measurement
are built into `outcomeLaw`. Exact scalar arithmetic and arbitrary one- and two-qubit gates
are the oracle-relative cost model of Lemma 1, p.8. The executed resource counts, including
oracle calls, are polynomial in the total qubit count, uniformly in the target and branch.

We choose gamma = 1 and round the suffix size with `suffixSize`: k = min(n, ceil(2 log_2
(max(2,n)))). Thus r+k=n without truncated subtraction in register types. The full-Hadamard
oracle fiber receives the suffix Hadamard correction (Remark 7, p.10); a zero fiber has
zero accepting effect. The Haar-good set and additive vanishing error work for every
mixed lab state simultaneously. This states p.3's additive soundness, not Theorem 5's
stronger multiplicative implication. -/
theorem robustCertification_twoBases :
    ∃ program : (r k : ℕ) → Bool → Qubits r → AmplitudeProgram (r + k) k,
    ∃ p : Polynomial ℕ, ∃ C : ℝ, ∃ n0 : ℕ, ∃ eta : ℕ → ℝ,
    ∃ good : (n : ℕ) → Set (EuclideanSpace ℂ (Qubits n)),
      program = conditionalMeasurementProgram ∧
      0 < C ∧ 1 ≤ n0 ∧ (∀ n, 0 ≤ eta n) ∧
      Filter.Tendsto eta Filter.atTop (nhds 0) ∧
      (∀ n, MeasurableSet (good n) ∧ ∀ psi ∈ good n, IsState psi) ∧
      (∀ n, n0 ≤ n →
        haarTargetLaw n (good n)ᶜ ≤ ENNReal.ofReal (C * ((2 : ℝ) ^ n)⁻¹)) ∧
      (∀ r k : ℕ, k = suffixSize (r + k) →
        ∀ psi : EuclideanSpace ℂ (Qubits (r + k)), IsState psi →
        ∀ (had : Bool) (z : Qubits r),
          let result := amplitudeProgramLaw (amplitudeOracle psi) (program r k had z)
            (initialAmplitudeExecution (r + k) k)
          result.failed = false ∧
          result.queries = List.ofFn (fun w : Fin (2 ^ k) =>
            (had, Fin.append z ((bitsEquivFin k).symm w))) ∧
          (∀ j : Fin 4, testResources r k had z (amplitudeOracle psi) j ≤ p.eval (r + k)) ∧
          compiledSuffixEffect r k had z (amplitudeOracle psi) =
            conditionalProjector r k psi had z) ∧
      (∀ r k : ℕ, k = suffixSize (r + k) → n0 ≤ r + k →
        ∀ psi : EuclideanSpace ℂ (Qubits (r + k)), IsState psi → psi ∈ good (r + k) →
        ∀ rho : Matrix (Qubits (r + k)) (Qubits (r + k)) ℂ, IsDensityMatrix rho →
          (pureDensity psi * rho).trace.re ≤ outcomeLaw r k psi rho true ∧
          (1 - (pureDensity psi * rho).trace.re) / 2 - eta (r + k) ≤
            outcomeLaw r k psi rho false) := by sorry

end QAlgorithms.Papers.RoadmapL06
