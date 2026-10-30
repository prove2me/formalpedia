-- Prove2me | Theorems.Thm_PlotkinShmoysTardos_general_relaxed_decision
-- name    : PlotkinShmoysTardos.general_relaxed_decision
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:56:06.232426+00:00
-- url     : https://prove2.me/theorems/e732ad0a-d4e5-4b57-8a21-44e5f8e9d5b6
-- title:
--   Theorem 4.5 — relaxed decision for GENERAL in $O(\rho^2\varepsilon^{-2}\log(m\rho\varepsilon^{-1}))$ oracle calls (corrected: test $\lambda\le\varepsilon$ before the first call)
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $A$ be a real $m\times n$ matrix with $m\ge1$, $b\in\mathbb R^m$, $d\in\mathbb R^m$ with $d>0$, $P\subseteq\mathbb R^n$ convex, and $\rho$ a width bound ($|a_ix-b_i|\le\rho d_i$ for all $i$ and $x\in P$). Let $O$ be any subroutine (10) for $P$ and $A$, let $x_0\in P$ and $0<\varepsilon<1$. Run the relaxed decision procedure: repeated calls to IMPROVE-GENERAL starting from $x_0$, stopping with the $\varepsilon$-approximate solution $x$ when $\lambda(x)\le\varepsilon$, and with the answer *infeasible* when $\lambda(x)>\varepsilon$ and the last call stopped because G2 held. Then the procedure stops, and at that point:
--   1. if it outputs a point $x$, then $x\in P$ and $Ax\le b+\varepsilon d$;
--   2. if it outputs *infeasible*, then no $z\in P$ satisfies $Az\le b$;
--   3. it has made at most
--   $$
--   C\,\rho^2\varepsilon^{-2}\bigl(1+\ln\max(1,\,m\rho\varepsilon^{-1})\bigr)
--   $$
--   calls to the subroutine (10);
--   4. the number of iterates whose $Ax$ it has computed is at most the number of calls plus one.
--
--   The paper states the count as $O(\rho^2\varepsilon^{-2}\log(m\rho\varepsilon^{-1}))$ calls "plus the time to compute $Ax$ for the current iterate $x$ between consecutive calls". The bound does not depend on $n$ or on the description of $P$: it is the width-dependent Lagrangean relaxation bound underlying fast approximate packing, covering and multicommodity flow algorithms.
--
--   Differences from the source:
--   - correction: the driver starts by calling IMPROVE-GENERAL with any point in P → the test λ ≤ ε is made before every call, including the first; reason: for m = n = 1, P = {0}, A = 1, b = 0, d = 1, x₀ = 0 (an exact solution) λ₀ = 0 and α = 4λ₀⁻¹ln(6mρλ₀⁻¹) is undefined; the extra test only skips calls the paper would make with λ₀ ≤ ε
--   - reading: O(ρ²ε⁻² log(mρε⁻¹)) calls → ≤ C ρ²ε⁻²(1 + ln max(1, mρε⁻¹)) with one absolute C chosen before the instance; reason: the literal form is false for every C: m = n = 1, P = {(1+δ)ε}, A = 1, b = 0, d = 1 gives ρ = λ₀ = (1+δ)ε > ε, at least one call, and Cρ²ε⁻²log(mρε⁻¹) → 0 as δ → 0; the two agree up to C when mρ/ε ≥ e
--   - reading: plus the time to compute Ax for the current iterate x between consecutive calls (model: exact real arithmetic, exponentiation as one step, p. 5) → the run counts the iterates whose Ax is computed (x₀ and every new iterate), at most calls + 1; arithmetic and exponentiation are free; reason: the paper's model charges unit cost for arithmetic and exponentiation; the remaining costs are the calls and the Ax evaluations
--   - reading: If λ > ε and condition G2 is satisfied → λ > ε and the last call returned through its G2 test; reason: the G2 test of the call is the one made with the call's α at an iterate with λ ≥ λ₀/2, where G1 holds and Lemma 4.1 applies
--   - reading: Figure 4 loop test 'x and y do not satisfy G2', then 'find a minimum-cost point x̃' → y is the dual of the current x for the call's fixed α, C_G(y) is the cost yᵗ(Ax̃ − b) of the oracle point x̃ = O(y), and the body reuses that x̃: one oracle call per evaluation of the test; reason: the figure computes y inside the body; the dual of the current x is the only y defined at the test, and x̃ attains C_G(y)
--   - generalization: ρ = maxᵢ max_{x∈P} |aᵢx − bᵢ|/dᵢ, the exact width → any ρ with |aᵢx − bᵢ| ≤ ρdᵢ for all i and x ∈ P (IsWidthBound), used by the algorithm; reason: the exact width satisfies the bound, so the Lean statement specializes to the paper's; it also avoids assuming the max is attained
--   - encoding: log → Real.log (natural logarithm); reason: a change of base only changes the constant C
--   - encoding: rows i = 1, …, m → m ≥ 1 ([NeZero m]); reason: maxᵢ over no rows is undefined in the paper; excludes only that undefined case
--   - encoding: the algorithm finds … or proves … → some step count k at which the run's phase is done, with both output guarantees and both counts at that step; reason: Lean definitions are total; termination becomes the existence of a halting step, and a halted run never changes
-- source:
--   Plotkin, Shmoys, Tardos, Fast Approximation Algorithms for Fractional Packing and Covering Problems, Cornell ORIE Technical Report No. 999 (Feb. 1992), Theorem 4.5, p. 27; driver paragraph, §4, p. 27; Figure 4, p. 25; model of computation, §1, p. 5

import Mathlib
import Definitions.Def_PlotkinShmoysTardos_General
import Definitions.Def_PlotkinShmoysTardos_relaxedOptimality
import Definitions.Def_PlotkinShmoysTardos_improveGeneral

namespace PlotkinShmoysTardos

/-- **Theorem 4.5.** Plotkin–Shmoys–Tardos, TR 999 (1992), p. 27: "For any `ε`, `0 < ε < 1`,
repeated calls to IMPROVE-GENERAL yields an algorithm that finds an `ε`-approximate solution to the
GENERAL problem or proves that no exact solution exists; the algorithm uses
`O(ρ²ε⁻² log(mρε⁻¹))` calls to the subroutine (10) for `P` and `A`, plus the time to compute `A x`
for the current iterate `x` between consecutive calls."
There is an absolute constant `C > 0` such that for every instance (`m ≥ 1`, `d > 0`, `P` convex,
`ρ` a width bound), every subroutine `O` for (10), every start point `x₀ ∈ P` and every
`0 < ε < 1`, the run of the procedure (`run`) stops after some number `k` of steps, and then
1. if it outputs `approx x`, `x` is an `ε`-approximate solution;
2. if it outputs `infeasible`, there is no exact solution;
3. it has made at most `C ρ² ε⁻² (1 + ln max(1, mρε⁻¹))` calls to `O`;
4. it has computed `A x` for at most one more iterate than it made calls. -/
theorem general_relaxed_decision :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m n : ℕ) [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
        (P : Set (Fin n → ℝ)) (ρ : ℝ) (O : (Fin m → ℝ) → (Fin n → ℝ)) (x₀ : Fin n → ℝ) (ε : ℝ),
        (∀ i, 0 < d i) → Convex ℝ P → IsWidthBound A b d P ρ → IsMinOracle A P O → x₀ ∈ P →
        0 < ε → ε < 1 →
        ∃ k : ℕ,
          (∃ o, (run A b d ρ O ε x₀ k).phase = Phase.done o) ∧
          (∀ x, (run A b d ρ O ε x₀ k).phase = Phase.done (Output.approx x) →
            IsApprox A b d P ε x) ∧
          ((run A b d ρ O ε x₀ k).phase = Phase.done Output.infeasible →
            ¬ ∃ z, IsExact A b P z) ∧
          ((run A b d ρ O ε x₀ k).cs.calls : ℝ) ≤
            C * ρ ^ 2 / ε ^ 2 * (1 + Real.log (max 1 (m * ρ / ε))) ∧
          (run A b d ρ O ε x₀ k).cs.evals ≤ (run A b d ρ O ε x₀ k).cs.calls + 1 := by sorry

end PlotkinShmoysTardos
