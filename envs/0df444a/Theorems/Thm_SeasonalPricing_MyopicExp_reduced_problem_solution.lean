-- Prove2me | Theorems.Thm_SeasonalPricing_MyopicExp_reduced_problem_solution
-- name    : SeasonalPricing.MyopicExp.reduced_problem_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:16:18.01615+00:00
-- url     : https://prove2.me/theorems/a22a8542-7add-47d5-afd7-8c626f9649c0
-- title:
--   Proof of Proposition 3 — the solution $p_1^* = 2 - T/e$, $p_2^* = p_1^* - 1$, value $\lambda e^{-1+T/e}$
-- statement:
--   Let $\lambda > 0$ and $0 < T \le 1$, and consider
--
--   $$
--   f(p_1, p_2) = p_2 \cdot \lambda e^{-p_2} + (p_1 - p_2)\cdot \lambda T e^{-p_1}, \qquad p_2 \le p_1 .
--   $$
--
--   Put $p_1^* = 2 - T/e$ and $p_2^* = p_1^* - 1$. Then
--
--   1. $p_2^* \le p_1^*$ and $f(p_1^*, p_2^*) = \lambda e^{-1 + T/e}$;
--   2. $f(p_1, p_2) \le \lambda e^{-1+T/e}$ for all real $p_2 \le p_1$;
--   3. $(p_1^*, p_2^*)$ is the only pair $p_2 \le p_1$ attaining this value;
--   4. $p_1^* \ge 1$ and $p_2^* \le 1$.
--
--   This is the solution of the reduced problem in the paper's proof of Proposition 3, which gives $\pi^*_{C/N} = \lambda e^{-1+T/e}$.
--
--   **Formalization Note** The paper writes "The solution to the latter problem is $p_1^* = 2 - T/e \ge 1$, $p_2^* = p_1^* - 1 \le 1$", asserting uniqueness without proof; uniqueness holds for $T > 0$ (at $T = 0$ every $p_1 \ge 1$ with $p_2 = 1$ is optimal), hence the hypothesis $0 < T$. The maximum is taken over all real $p_2 \le p_1$, as printed.
-- source:
--   Aviv and Pazgal, Optimal Pricing of Seasonal Products in the Presence of Forward-Looking Consumers, Manufacturing & Service Operations Management 10(3), 2008, pp. 358–359, Proof of Proposition 3 (the solution of the reduced problem)

import Mathlib

namespace SeasonalPricing.MyopicExp

/-- Proof of Proposition 3 (Aviv–Pazgal 2008, pp. 358–359), the solution of the reduced problem
`max_{p₁, p₂ ≤ p₁} {p₂ · λe^{−p₂} + (p₁ − p₂) · λTe^{−p₁}}` for `λ > 0`, `0 < T ≤ 1`:
the maximum value is `λe^{−1+T/e}`, it is attained at `p₁* = 2 − T/e`, `p₂* = p₁* − 1`, and only
there; moreover `p₁* ≥ 1` and `p₂* ≤ 1`. -/
theorem reduced_problem_solution (lam T : ℝ) (hlam : 0 < lam) (hT0 : 0 < T) (hT1 : T ≤ 1) :
    let f : ℝ → ℝ → ℝ := fun p1 p2 =>
      p2 * lam * Real.exp (-p2) + (p1 - p2) * lam * T * Real.exp (-p1)
    let p1star : ℝ := 2 - T / Real.exp 1
    let p2star : ℝ := p1star - 1
    p2star ≤ p1star ∧
    f p1star p2star = lam * Real.exp (-1 + T / Real.exp 1) ∧
    (∀ p1 p2 : ℝ, p2 ≤ p1 → f p1 p2 ≤ lam * Real.exp (-1 + T / Real.exp 1)) ∧
    (∀ p1 p2 : ℝ, p2 ≤ p1 → f p1 p2 = lam * Real.exp (-1 + T / Real.exp 1) →
      p1 = p1star ∧ p2 = p2star) ∧
    1 ≤ p1star ∧ p2star ≤ 1 := by sorry

end SeasonalPricing.MyopicExp
