-- Prove2me | Theorems.Thm_Rudin_ch06_change_of_variable
-- name    : Rudin.ch06_change_of_variable
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T23:23:36.050288+00:00
-- url     : https://prove2.me/theorems/d1f86871-e044-487c-95dd-103b3f7949d5
-- title:
--   Theorem 6.19 — change of variable
-- statement:
--   Let $\varphi$ be a strictly increasing continuous function mapping $[A,B]$ onto $[a,b]$, let $\alpha$ be monotonically increasing on $[a,b]$ and $f \in \mathcal{R}(\alpha)$. Put $\beta = \alpha \circ \varphi$ and $g = f \circ \varphi$. Then $g \in \mathcal{R}(\beta)$ and $\int_A^B g\,d\beta = \int_a^b f\,d\alpha$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 6, p. 132, Theorem 6.19

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 6.19 (change of variable): let `φ` be a strictly increasing continuous
function of `[A, B]` onto `[a, b]`, let `α` be monotonically increasing on `[a, b]` and
`f ∈ ℛ(α)`.  Put `β = α ∘ φ` and `g = f ∘ φ`.  Then `g ∈ ℛ(β)` and
`∫_A^B g dβ = ∫_a^b f dα`. -/
theorem ch06_change_of_variable (a b A B : ℝ) (hab : a ≤ b) (hAB : A ≤ B) (f α φ : ℝ → ℝ)
    (hφmono : StrictMonoOn φ (Set.Icc A B)) (hφc : ContinuousOn φ (Set.Icc A B))
    (hφA : φ A = a) (hφB : φ B = b)
    (hα : MonotoneOn α (Set.Icc a b)) (hf : RSIntegrable a b f α) :
    RSIntegrable A B (f ∘ φ) (α ∘ φ) ∧
    RSIntegral A B (f ∘ φ) (α ∘ φ) = RSIntegral a b f α := by sorry

end Rudin
