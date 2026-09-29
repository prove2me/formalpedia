-- Prove2me | Theorems.Thm_SiegelFields_commutator_eq_cross
-- name    : SiegelFields.commutator_eq_cross
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T01:21:32.220423+00:00
-- url     : https://prove2.me/theorems/6f314db1-5335-4b2d-af76-c177666f3e49
-- title:
--   The cross product is the commutator: $[V,W]=\sqrt2\,i\,V\times W$
-- statement:
--   For all $v,w\in\mathbb R^3$, with $V(\cdot)$ the book's basis map,
--
--   $$[V(v),V(w)]=V(v)V(w)-V(w)V(v)=\sqrt2\,i\;V(v\times w),$$
--
--   where $v\times w$ is the usual cross product of $\mathbb R^3$. Hence the cross product is a special case of the Lie bracket (commutator).
-- source:
--   W. Siegel, *Fields*, arXiv:hep-th/9912205v3 (2005), https://arxiv.org/abs/hep-th/9912205, Chapter II (Spin), Section A (Two components), §IIA1 p. 112

import Mathlib
import Definitions.Def_SiegelFields_SpinDefs

open Matrix Complex

namespace SiegelFields
theorem commutator_eq_cross (v w : Fin 3 → ℝ) :
    vecToMatrix v * vecToMatrix w - vecToMatrix w * vecToMatrix v =
      ((Real.sqrt 2 : ℂ) * I) • vecToMatrix (crossProduct v w) := by sorry
end SiegelFields
