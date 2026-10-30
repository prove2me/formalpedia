-- Prove2me | Theorems.Thm_PlotkinShmoysTardos_theorem_4_4
-- name    : PlotkinShmoysTardos.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:54:44.174212+00:00
-- url     : https://prove2.me/theorems/e08abb83-dc3a-4e56-a280-7adf838a1a85
-- title:
--   Theorem 4.4 — IMPROVE-GENERAL terminates in $O(\rho^2\lambda_0^{-2}\log(m\rho\lambda_0^{-1}))$ iterations
-- statement:
--   There is an absolute constant $C>0$ with the following property. Take any instance of the GENERAL problem ($m\ge1$ rows, $d>0$, $P$ convex, $\rho$ a width bound), any subroutine $O$ for (10), and any $x\in P$ with $\lambda_0=\lambda(x)>0$. Then the call IMPROVE-GENERAL$(x)$ returns, and the number of calls to the subroutine it makes is at most
--   $$
--   C\,\rho^2\lambda_0^{-2}\bigl(1+\ln(m\rho\lambda_0^{-1})\bigr).
--   $$
--   The number of calls equals the number of iterations, plus one when the call returns through G2. The paper states the bound as $O(\rho^2\lambda_0^{-2}\log(m\rho\lambda_0^{-1}))$ iterations. Summed over the calls of the driver, it gives Theorem 4.5.
--
--   Differences from the source:
--   - reading: O(ρ²λ₀⁻² log(mρλ₀⁻¹)) → ≤ C ρ²λ₀⁻²(1 + ln(mρλ₀⁻¹)) with one absolute C chosen before the instance; reason: the literal form is false: m = 1, P = [−1, 1], A = 1, b = 0, d = 1, x = 1 gives λ₀ = ρ = 1, log(mρλ₀⁻¹) = 0, yet G2 fails (2y > y/5), so an iteration runs; the two agree up to C when mρ/λ₀ ≥ e
--   - reading: iterations → calls to the subroutine made by the call; reason: each iteration makes one call, and one more call is made by the final G2 test; the extra call is absorbed in C since the bound is at least C
--   - reading: Figure 4 loop test 'x and y do not satisfy G2', then 'find a minimum-cost point x̃' → y is the dual of the current x for the call's fixed α, C_G(y) is the cost yᵗ(Ax̃ − b) of the oracle point x̃ = O(y), and the body reuses that x̃: one oracle call per evaluation of the test; reason: the figure computes y inside the body; the dual of the current x is the only y defined at the test, and x̃ attains C_G(y)
--   - generalization: ρ = maxᵢ max_{x∈P} |aᵢx − bᵢ|/dᵢ, the exact width → any ρ with |aᵢx − bᵢ| ≤ ρdᵢ for all i and x ∈ P (IsWidthBound), used by the algorithm; reason: the exact width satisfies the bound, so the Lean statement specializes to the paper's; it also avoids assuming the max is attained
--   - encoding: log → Real.log (natural logarithm); reason: a change of base only changes the constant C
--   - encoding: α = 4λ₀⁻¹ln(6mρλ₀⁻¹) → 0 < λ₀; reason: α is undefined otherwise; the driver only calls with λ₀ > ε > 0
--   - encoding: rows i = 1, …, m → m ≥ 1 ([NeZero m]); reason: maxᵢ over no rows is undefined in the paper; excludes only that undefined case
--   - encoding: terminates → some step count k at which the call's exit tag is not running (Nat.iterate of the step function); reason: Lean definitions are total; termination becomes the existence of a halting step
-- source:
--   Plotkin, Shmoys, Tardos, Fast Approximation Algorithms for Fractional Packing and Covering Problems, Cornell ORIE Technical Report No. 999 (Feb. 1992), Theorem 4.4, p. 27

import Mathlib
import Definitions.Def_PlotkinShmoysTardos_General
import Definitions.Def_PlotkinShmoysTardos_relaxedOptimality
import Definitions.Def_PlotkinShmoysTardos_improveGeneral

namespace PlotkinShmoysTardos

/-- **Theorem 4.4.** Plotkin–Shmoys–Tardos, TR 999 (1992), p. 27: "The procedure IMPROVE-GENERAL
terminates in `O(ρ²λ₀⁻² log(mρλ₀⁻¹))` iterations."
There is an absolute constant `C > 0` such that for every instance (`m ≥ 1`, `d > 0`, `P` convex,
`ρ` a width bound), every subroutine `O` for (10) and every `x ∈ P` with
`λ₀ = maxᵢ (aᵢ x − bᵢ)/dᵢ > 0`, the call IMPROVE-GENERAL(x) returns after a number of oracle
calls (one per evaluation of the loop test that reaches the G2 check, hence at least the number of
iterations) of at most `C ρ² λ₀⁻² (1 + ln(mρλ₀⁻¹))`. -/
theorem theorem_4_4 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m n : ℕ) [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
        (P : Set (Fin n → ℝ)) (ρ : ℝ) (O : (Fin m → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ),
        (∀ i, 0 < d i) → Convex ℝ P → IsWidthBound A b d P ρ → IsMinOracle A P O → x ∈ P →
        0 < lam A b d x →
        ∃ k, (callRun A b d ρ O x k).tag ≠ Tag.running ∧
          ((callRun A b d ρ O x k).calls : ℝ) ≤
            C * ρ ^ 2 / (lam A b d x) ^ 2 * (1 + Real.log (m * ρ / lam A b d x)) := by sorry

end PlotkinShmoysTardos
