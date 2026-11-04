-- Prove2me | Theorems.Thm_StochHiddenConvex_proposition_2_1
-- name    : StochHiddenConvex.proposition_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:53:37.774479+00:00
-- url     : https://prove2.me/theorems/b7ab9a86-d93e-4603-869f-204cbeaeabd3
-- title:
--   Proposition 2.1: $F=G\circ g$, $G=F\circ g^{-1}$, and convexity of $G$ (corrected: $g_i$ continuous)
-- statement:
--   Assume the coordinates of $\xi$ are independent (Assumption 2.1(a)), each $\phi_i(\cdot,\xi_i)$ is non-decreasing on $[\underline X_i,\bar X_i]$ (2.1(b)), each $g_i$ is continuous on $[\underline X_i,\bar X_i]$, and the expectations of $\phi_i(x_i,\xi_i)$ and $f(\phi(x,\xi))$ exist for $x\in\mathcal X$. Then
--
--   1. $F(x)=G(g(x))$ for all $x\in\mathcal X$;
--   2. $G(u)=F(g^{-1}(u))$ for all $u\in\mathcal U$;
--   3. if moreover Assumption 2.1(c) holds and $f$ is convex, then $G$ is convex on $\mathcal U$;
--   4. if moreover Assumption 2.1(c) holds and $f$ is component-wise convex, then $G$ is component-wise convex on $\mathcal U$.
--
--   So problem (3) has the same optimal value as (1) and is a convex problem in $u$: this is the hidden convexity that MSG exploits, and step (f) of the proof of Theorem 3.2 rests on it.
--
--   Differences from the source:
--   - correction: Assumption 2.1(a)(b) only → in addition, every gᵢ is continuous on [X̲ᵢ, X̄ᵢ]; reason: without it clause 1 fails: d = 1, 𝒳 = [−1, 1], ϕ(x, ξ) = 1[x > 0], f(y) = y satisfy 2.1(a)(b), but at x = 1/2, F(x) = 1 while g⁻¹(g(x)) = 0 and G(g(x)) = 0; continuity is implied by Assumption 2.2(c) or 2.3(a) of the paper
--   - generalization: ϕᵢ(·, ξᵢ) non-decreasing (p.1, Assumption 2.1(b)), stated without a domain for x (read: all of ℝ^d) → required only for x ∈ 𝒳; reason: a condition on ℝ^d implies the same condition on 𝒳, so the statement specializes to the ℝ^d reading; Assumption 2.3 is itself stated on 𝒳 (g : 𝒳 → 𝒰)
--   - reading: for any ξ ∈ Ξ (Assumptions 2.1(b), 2.2(c)) → for ℙ-almost every ξ; reason: Ξ ⊆ ℝ^d is the unspecified set of values of ξ, a set of probability one; the conditions enter only through expectations
--   - encoding: ϕ a random function; 𝔼ϕ(x, ξ) taken without comment; 𝒳 = [X̲₁, X̄₁] × … × [X̲_d, X̄_d] → ϕᵢ jointly measurable, ϕᵢ(xᵢ, ·) integrable for x ∈ 𝒳, X̲ᵢ ≤ X̄ᵢ (RegularData); reason: the field's standing measurability convention; excludes only data for which the paper's expectations or intervals are undefined
--   - encoding: the expectations F(x), G(u) for f merely convex or component-wise convex → f(ϕ(x, ·)) integrable for x ∈ 𝒳 (IntegrableObjective); reason: F is the objective of problem (1) and is finite; excludes only data for which it is undefined
--   - reading: f is convex (component-wise convex) in x ∈ 𝒳 → f convex (component-wise convex) on all of ℝ^d; reason: f is evaluated at ϕ(x, ξ) ∈ ℝ^d, not on 𝒳; p.1 assumes f convex without restriction
--   - encoding: Ŷ(x₁), Ŷ(x₂) defined on a common probability space; ≤_cv the concave order (footnote 1, p.9) → a coupling probability measure on ℝ × ℝ with the two laws as marginals; the published concave order MDPFinance.StructuredModels.LEConcaveOrder; reason: a pair on a common space is the same as its joint law; LEConcaveOrder is the concave order (concave test functions integrable under both laws)
-- source:
--   X. Chen, N. He, Y. Hu, Z. Ye, Efficient Algorithms for A Class of Stochastic Hidden Convex Optimization and Its Applications in Network Revenue Management, arXiv:2205.01774v3, Proposition 2.1, p.9

import Mathlib
import Definitions.Def_StochHiddenConvex_Model_Assumptions
import Definitions.Def_StochHiddenConvex_ComponentwiseConvexOn

open MeasureTheory

namespace StochHiddenConvex

/-- **Proposition 2.1 (convex reformulation).** Chen, He, Hu & Ye, arXiv:2205.01774v3,
Proposition 2.1, p.9 (cited from Feng and Shanthikumar 2018): "Under Assumption 2.1(a)(b),
problem (3) has the same objective value as problem (1) via the variable change, i.e.,
F(x) = G(g(x)), ∀x ∈ 𝒳 and G(u) = F(g⁻¹(u)), ∀u ∈ 𝒰. Additionally, if Assumption 2.1(c) holds
and f is convex (component-wise convex) in x ∈ 𝒳, then G is convex (component-wise convex) in
u ∈ 𝒰."

All four clauses.

**Formalization Note.** Corrected: each `gᵢ` is continuous on `[X̲ᵢ, X̄ᵢ]` (otherwise the first
clause fails: `d = 1`, `𝒳 = [−1, 1]`, `ϕ(x, ξ) = 1[x > 0]`, `f(y) = y`, `x = 1/2` give
`F(x) = 1` but `G(g(x)) = 0`). Expectations exist (`RegularData`, `IntegrableObjective`). -/
theorem proposition_2_1 {d : ℕ} (M : Model d) [IsProbabilityMeasure M.P]
    (hreg : M.RegularData) (hobj : M.IntegrableObjective)
    (h21a : M.Assumption21a) (h21b : M.MonotoneOnBox)
    (hcont : ∀ i, ContinuousOn (M.gc i) (Set.Icc (M.lo i) (M.hi i))) :
    (∀ x ∈ M.box, M.F x = M.G (M.g x)) ∧
    (∀ u ∈ M.Ubox, M.G u = M.F (M.ginv u)) ∧
    (M.Assumption21c → ConvexOn ℝ Set.univ M.f → ConvexOn ℝ M.Ubox M.G) ∧
    (M.Assumption21c → ComponentwiseConvexOn Set.univ M.f →
      ComponentwiseConvexOn M.Ubox M.G) := by sorry

end StochHiddenConvex
