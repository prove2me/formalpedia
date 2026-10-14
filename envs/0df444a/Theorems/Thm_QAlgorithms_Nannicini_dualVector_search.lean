-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_dualVector_search
-- name    : QAlgorithms.Nannicini.dualVector_search
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:53:43.371153+00:00
-- url     : https://prove2.me/theorems/84c55d7b-d5e4-4af7-8924-818b102dd732
-- title:
--   Computing the dual vector with Õ(√m) calls to a trace-estimate oracle (corrected statement)
-- statement:
--   This is a corrected, precise form of the informal Proposition 8.21.
--
--   Consider SDP data: Hermitian $n\times n$ matrices $C, A^{(1)},\dots,A^{(m)}$ and $b\in\mathbb{R}^m$, under the standing assumptions (a) $A^{(1)}=I$, $b_1=R>0$; (b) $\|C\|\le 1$; (c) (D-SDP) has an optimal solution $y$ with $\|y\|_1\le r$, where $r\ge 1$. Fix $\gamma\in\mathbb{R}$, and let $P_\epsilon(X)$ be the PIC polytope (8.16). Let $X\succeq 0$ with $\operatorname{Tr}X\le R$, $\rho = X/\operatorname{Tr}X$, $\theta\ge 0$, and let $\tilde c\in\mathbb{R}$ satisfy $|\operatorname{Tr}(C\rho)-\tilde c|\le\theta$.
--
--   Numbers are held in registers as $p$-bit fixed-point numbers $z\mapsto(\mathrm{int}(z)-2^{p-1})/2^f$. The algorithm has access to two unitaries on an index register of $\lceil\log_2 m\rceil$ qubits, a $p$-qubit value register and a $g$-qubit garbage register:
--
--   1. $U|j\rangle|0\rangle|0\rangle = |j\rangle|\tilde a_j\rangle|\psi_j\rangle$ with $|\operatorname{Tr}(A^{(j)}\rho)-\tilde a_j|\le\theta$ and unit vectors $\psi_j$;
--   2. $B|j\rangle|0\rangle|0\rangle = |j\rangle|b_j\rangle|\phi_j\rangle$, giving the entries of $b$ exactly.
--
--   The numbers $\gamma, r, \theta, \tilde c$ are given classically. Then there are absolute constants $K>0$ and $e\in\mathbb{N}$ such that for all $m\ge 1$, $p, f, g$, $\delta\in(0,1)$ and $\gamma,r,\theta,\tilde c$ there is a quantum circuit over two-qubit gates, followed by a computational-basis measurement and a classical output map, which uses at most
--
--   $$
--   K\sqrt{m}\,\bigl(\ln(2+m)+\ln(2+1/\delta)+p+1\bigr)^{e}
--   $$
--
--   calls to $U$, the same number of calls to $B$, and the same number of gates, and such that for every instance as above, with probability at least $1-\delta$, either it returns a vector in $P_{4Rr\theta}(X)\cap\{y:\|y\|_1\le r\}$, or it returns “failure” and $P_0(X)\cap\{y:\|y\|_1\le r\}=\emptyset$.
--
--   In particular, when $P_0(X)\cap\{\|y\|_1\le r\}$ is nonempty the algorithm returns, with probability at least $1-\delta$, a vector of $P_{4Rr\theta}(X)\cap\{\|y\|_1\le r\}$. This is the dual-vector step of the quantum MMWU SDP solver, and it gives the $\sqrt{m}$ dependence of its running time.
--
--   **Formalization Note** Calls to $U$ and $B$ include inverse and controlled calls. The classical map from measurement outcomes to the returned vector is not costed. The circuit depends only on $m,p,f,g,\delta,\gamma,r,\theta,\tilde c$, never on $A, b, C, X$ or $n$.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 195, Proposition 8.21. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_QAlgorithms_Nannicini_Ch08a_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open QAlgorithms.SDP

open scoped ComplexOrder








open Classical in
/-- Corrected statement. Nannicini p.195, Proposition 8.21 (informal; the source defers the precise
version to Lem. 16 of [van Apeldoorn et al., 2020b], not on disk). Printed: given a circuit `U`
with `U|j⟩|0⟩|0⟩ = |j⟩|ã_j⟩|ψ_j⟩`, `|Tr(A^(j)ρ) − ã_j| ≤ θ`, a quantum algorithm with `Õ(√m)`
calls to `U` and as many gates "with high probability returns a vector in
`P_{4Rrθ}(X) ∩ {‖y‖₁ ≤ r}` if `P_0(X) ∩ {‖y‖₁ ≤ r}` is nonempty, and returns 'failure' if
`P_0(X) ∩ {‖y‖₁ ≤ r}` is empty".

Changes, each forced by a gap of the printed claim:
1. *High probability*: success probability `≥ 1 − δ` for every `δ ∈ (0,1)`, with cost
   polylogarithmic in `1/δ` (the reading of Rem. 8.20, p.194).
2. *`Õ(√m)`*: `K √m (ln(2+m) + ln(2+1/δ) + p + 1)^e` with absolute `K, e` quantified first; the
   suppressed factors are polylogarithmic in `m`, `1/δ` and polynomial in the word size `p`.
3. *Cost model*: the algorithm is an oracle circuit over all two-qubit unitaries
   (`twoQubitGateSet`), started in `|0…0⟩`, measured in the computational basis, the outcome
   mapped classically to a vector or `none` ("failure"); calls to `U` (plain, inverse or
   controlled) are `queryCount 0`. Numbers are `p`-bit fixed point (`fixedPointVal`).
4. *Missing inputs*: the procedure (pp.194–195) needs `c̃` with `|Tr(Cρ) − c̃| ≤ θ` (Prop. 8.19)
   and the points `b_j`; `c̃, γ, r, θ` are given classically, and `b` through an exact oracle `B`
   of the same form (index `1`), whose calls are bounded too (loading `b` into gates would cost
   `Θ(m)` gates, so the gate claim needs this access).
5. *Failure clause*: the algorithm only sees `θ`-accurate traces, so it cannot detect emptiness
   of `P_0(X)`, which is defined by exact traces. Stated instead: failure is returned only when
   `P_0(X) ∩ {‖y‖₁ ≤ r}` is empty (when it is empty, the output is failure or a vector of
   `P_{4Rrθ}(X) ∩ {‖y‖₁ ≤ r}`), which is what the procedure through Prop. 8.19 gives.

The algorithm depends on `m, p, f, g, δ, γ, r, θ, c̃` only, never on `A, b, C, X, n`. Standing
assumptions (a), (b), (c) and the hypotheses of Prop. 8.19 are binders. -/
theorem dualVector_search :
    ∃ (K : ℝ) (e : ℕ), 0 < K ∧
    ∀ (m : ℕ) (hm : 0 < m) (p f g : ℕ) (δ : ℝ), 0 < δ → δ < 1 → ∀ (γ r θ ctil : ℝ),
    ∃ (N : ℕ) (c : OracleCircuit twoQubitGateSet (fun _ : Fin 2 => Nat.clog 2 m + p + g) N)
      (out : Qubits N → Option (Fin m → ℝ)),
      (c.queryCount 0 : ℝ) ≤
        K * Real.sqrt m * (Real.log (2 + m) + Real.log (2 + 1 / δ) + p + 1) ^ e ∧
      (c.queryCount 1 : ℝ) ≤
        K * Real.sqrt m * (Real.log (2 + m) + Real.log (2 + 1 / δ) + p + 1) ^ e ∧
      (c.gateCount : ℝ) ≤
        K * Real.sqrt m * (Real.log (2 + m) + Real.log (2 + 1 / δ) + p + 1) ^ e ∧
      ∀ (n : ℕ) (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (b : Fin m → ℝ)
        (C : Matrix (Fin n) (Fin n) ℂ) (R : ℝ),
        (∀ j, (A j).IsHermitian) → C.IsHermitian → A ⟨0, hm⟩ = 1 → b ⟨0, hm⟩ = R → 0 < R →
        specNorm C ≤ 1 → 1 ≤ r → (∃ y : Fin m → ℝ, IsDualOptimal A C b y ∧ ∑ j, |y j| ≤ r) →
        ∀ X : Matrix (Fin n) (Fin n) ℂ, X.PosSemidef → X.trace.re ≤ R → 0 ≤ θ →
        |(C * ((X.trace)⁻¹ • X)).trace.re - ctil| ≤ θ →
        ∀ U B : Matrix (Qubits (Nat.clog 2 m + p + g)) (Qubits (Nat.clog 2 m + p + g)) ℂ,
        IsFixedPointValueOracle p f g (fun j => (A j * ((X.trace)⁻¹ • X)).trace.re) θ U →
        IsFixedPointValueOracle p f g b 0 B →
        probEvent (act (c.unitary fun k => if k = 0 then U else B) (zeroKet N))
          (fun z => (∃ y, out z = some y ∧
              y ∈ picPolytope A b C γ (4 * R * r * θ) X ∩ {y : Fin m → ℝ | ∑ j, |y j| ≤ r}) ∨
            (out z = none ∧ picPolytope A b C γ 0 X ∩ {y : Fin m → ℝ | ∑ j, |y j| ≤ r} = ∅)) ≥
          1 - δ := by
  sorry

end QAlgorithms.Nannicini
