-- Prove2me | Theorems.Thm_PDASNewton_FunSpace_reformulation_4_9_4_10
-- name    : PDASNewton.FunSpace.reformulation_4_9_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:59.076802+00:00
-- url     : https://prove2.me/theorems/d9f5b1eb-c4be-4875-8af9-8080363651ed
-- title:
--   (4.9)–(4.10), p. 14 — under (H2) and c = β, system (4.2) ⟺ βy* − βψ + max(0, Cy* − f + βψ) = 0 and λ* = f − Cy* − βy*
-- statement:
--   Let $(\Omega, \mu)$ be a finite measure space, $q > 2$, $\beta > 0$, $C \in \mathcal{L}(L^2(\Omega), L^q(\Omega))$, and let $A \in \mathcal{L}(L^2(\Omega))$ satisfy (H2): $A = C + \beta I$. Let $f, \psi, y^*, \lambda^* \in L^2(\Omega)$. Then $(y^*, \lambda^*)$ solves system (4.2) with $c = \beta$, that is $Ay^* + \lambda^* = f$ and $\lambda^* - \max(0, \lambda^* + \beta(y^* - \psi)) = 0$, if and only if, almost everywhere,
--   $$\beta y^* - \beta\psi + \max(0, Cy^* - f + \beta\psi) = 0 \tag{4.9}$$
--   $$\lambda^* = f - Cy^* - \beta y^*. \tag{4.10}$$
--
--   This eliminates the multiplier and turns the optimality system into one nonsmooth equation in $y$ alone, the equation the reduced algorithm solves.
--
--   **Formalization Note** (H2) is stated as $Ay = Cy + \beta y$ almost everywhere for every $y \in L^2$, which avoids constructing the inclusion $L^q \subseteq L^2$. The measure space generalizes the paper's bounded domain.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 14, (4.9)–(4.10); (H2) p. 13; (4.2) p. 12

import Mathlib
import Definitions.Def_PDASNewton_FunSpace_Setting

namespace PDASNewton.FunSpace

open MeasureTheory
open scoped ENNReal

/-- (4.9)–(4.10), p. 14: under (H2), for `c = β` the optimality system (4.2) is equivalent to
`β y* - β ψ + max(0, C y* - f + β ψ) = 0` and `λ* = f - C y* - β y*` (a.e.). -/
theorem reformulation_4_9_4_10 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : 2 < q)
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (β : ℝ) (hβ : 0 < β) (C : Lp ℝ 2 μ →L[ℝ] Lp ℝ q μ)
    (hAC : ∀ y : Lp ℝ 2 μ, (A y : α → ℝ) =ᵐ[μ] fun x => C y x + β * y x)
    (f ψ ystar lamstar : Lp ℝ 2 μ) :
    IsSolution A f ψ β ystar lamstar ↔
      ((∀ᵐ x ∂μ, β * ystar x - β * ψ x + max 0 (C ystar x - f x + β * ψ x) = 0) ∧
        ∀ᵐ x ∂μ, lamstar x = f x - C ystar x - β * ystar x) := by sorry

end PDASNewton.FunSpace
