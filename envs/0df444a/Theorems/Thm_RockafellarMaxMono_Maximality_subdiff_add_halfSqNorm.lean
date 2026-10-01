-- Prove2me | Theorems.Thm_RockafellarMaxMono_Maximality_subdiff_add_halfSqNorm
-- name    : RockafellarMaxMono.Maximality.subdiff_add_halfSqNorm
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T18:04:23.271634+00:00
-- url     : https://prove2.me/theorems/2dfe329b-f350-4a85-bbf9-1e3ce9eb38c9
-- title:
--   (3.1) — sum rule $\partial(f+j)(x) = \partial f(x) + \partial j(x)$
-- statement:
--   Let $E$ be a real Banach space, let $f$ be a lower semicontinuous proper convex function on $E$, and let $j(x) = \tfrac12\|x\|^2$. Then
--
--   $$
--   \partial(f+j)(x) = \partial f(x) + \partial j(x) \qquad \text{for every } x \in E ,
--   $$
--
--   where the right-hand side is the Minkowski sum $\{x_1^* + x_2^* \mid x_1^* \in \partial f(x),\ x_2^* \in \partial j(x)\}$ in $E^*$.
--
--   The sum rule holds here because $j$ is finite and continuous everywhere. In the proof of Theorem A it transfers information about $\partial(f+j)$ back to $\partial f$.
--
--   **Formalization Note** The paper prints "$\partial(f + j) = \partial f(x) + \partial j(x)$", omitting the argument $x$ on the left; we state the evident reading $\partial(f+j)(x)$. $f + j$ is the pointwise sum in $(-\infty,+\infty]$; the set sum uses Mathlib's pointwise addition of sets.
-- source:
--   Rockafellar, On the maximal monotonicity of subdifferential mappings, Pacific J. Math. 33 (1970), p. 213, (3.1)

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Definitions.Def_RockafellarMaxMono_Shared_HalfSqNorm
open Pointwise

namespace RockafellarMaxMono.Maximality

theorem subdiff_add_halfSqNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f) :
    ∀ x : E, Shared.subdiff (fun y => f y + Shared.halfSqNorm y) x = Shared.subdiff f x + Shared.subdiff Shared.halfSqNorm x := by sorry

end RockafellarMaxMono.Maximality
