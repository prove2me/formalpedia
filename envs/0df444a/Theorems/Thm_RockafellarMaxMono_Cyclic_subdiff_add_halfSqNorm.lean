-- Prove2me | Theorems.Thm_RockafellarMaxMono_Cyclic_subdiff_add_halfSqNorm
-- name    : RockafellarMaxMono.Cyclic.subdiff_add_halfSqNorm
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:12:20.772987+00:00
-- url     : https://prove2.me/theorems/854b9b99-e0a7-4c32-a66c-5c5b323d2da7
-- title:
--   (3.1) — sum rule $\partial(f + j)(x) = \partial f(x) + \partial j(x)$ with $j = \tfrac12\|\cdot\|^2$
-- statement:
--   Let $E$ be a real Banach space with dual $E^*$, let $f$ be a lower semicontinuous proper convex function on $E$, and let $j(x) = \tfrac12\|x\|^2$. Then for every $x \in E$,
--
--   $$
--   \partial (f + j)(x) = \partial f(x) + \partial j(x),
--   $$
--
--   where the right-hand side is the (Minkowski) sum $\{x_1^* + x_2^* \mid x_1^* \in \partial f(x),\ x_2^* \in \partial j(x)\}$ of subsets of $E^*$.
--
--   In the proof of Theorem B this rule, together with its counterpart for $g$, turns $\partial g \supset \partial f$ into $\partial (g+j) \supset \partial (f+j)$.
--
--   **Formalization Note** The paper prints the left-hand side as "$\partial(f + j)$" without the argument; we read it as $\partial(f+j)(x)$, which is what the quantifier "$\forall x \in E$" requires. The set sum is Mathlib's pointwise addition of sets.
-- source:
--   Rockafellar, On the maximal monotonicity of subdifferential mappings, Pacific J. Math. 33 (1970), p. 213, (3.1)

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Definitions.Def_RockafellarMaxMono_Shared_HalfSqNorm
open Pointwise

namespace RockafellarMaxMono.Cyclic

theorem subdiff_add_halfSqNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f) :
    ∀ x : E, Shared.subdiff (fun y => f y + Shared.halfSqNorm y) x = Shared.subdiff f x + Shared.subdiff Shared.halfSqNorm x := by sorry

end RockafellarMaxMono.Cyclic
