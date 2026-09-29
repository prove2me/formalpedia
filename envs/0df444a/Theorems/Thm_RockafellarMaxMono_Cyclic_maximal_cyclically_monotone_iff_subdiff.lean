-- Prove2me | Theorems.Thm_RockafellarMaxMono_Cyclic_maximal_cyclically_monotone_iff_subdiff
-- name    : RockafellarMaxMono.Cyclic.maximal_cyclically_monotone_iff_subdiff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:15:23.443224+00:00
-- url     : https://prove2.me/theorems/ead3de3a-47c7-4f61-a350-273f6f172e03
-- title:
--   Theorem B — subdifferentials of lsc proper convex functions are exactly the maximal cyclically monotone operators, unique up to a constant
-- statement:
--   Let $E$ be a real Banach space with dual $E^*$, and let $T : E \to E^*$ be a multivalued mapping. Then:
--
--   1. There exists a lower semicontinuous proper convex function $f$ on $E$ with $T = \partial f$ if and only if $T$ is a maximal cyclically monotone operator.
--   2. In this case $T$ determines $f$ uniquely up to an additive constant: if $f$ and $g$ are lower semicontinuous proper convex functions on $E$ with $T = \partial f$ and $T = \partial g$, then there is a real constant $c$ with
--   $$
--   g(x) = f(x) + c \qquad \text{for all } x \in E .
--   $$
--
--   Theorem B characterizes the subdifferential mappings of lower semicontinuous proper convex functions on a Banach space intrinsically, as the maximal cyclically monotone operators, and shows that such an operator has an essentially unique convex "potential". It completes an argument of Rockafellar's 1966 paper in which the maximality and uniqueness steps had a gap in the nonreflexive case.
--
--   **Formalization Note** $T = \partial f$ is equality of multivalued mappings, $T(x) = \partial f(x)$ for all $x$. Maximality is among cyclically monotone operators (see the definition). Both parts of the theorem are stated as one conjunction. The constant is real, so on points where $f = +\infty$ the uniqueness equation reads $g(x) = +\infty$.
-- source:
--   Rockafellar, On the maximal monotonicity of subdifferential mappings, Pacific J. Math. 33 (1970), p. 210, Theorem B

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Definitions.Def_RockafellarMaxMono_Cyclic_CyclicallyMonotone

namespace RockafellarMaxMono.Cyclic

theorem maximal_cyclically_monotone_iff_subdiff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (T : E → Set (StrongDual ℝ E)) :
    ((∃ f : E → EReal, Shared.ProperConvex f ∧ LowerSemicontinuous f ∧ ∀ x, T x = Shared.subdiff f x) ↔
        IsMaximalCyclicallyMonotone T) ∧
      ∀ f g : E → EReal, Shared.ProperConvex f → LowerSemicontinuous f →
        Shared.ProperConvex g → LowerSemicontinuous g →
        (∀ x, T x = Shared.subdiff f x) → (∀ x, T x = Shared.subdiff g x) →
        ∃ c : ℝ, ∀ x, g x = f x + (c : EReal) := by sorry

end RockafellarMaxMono.Cyclic
