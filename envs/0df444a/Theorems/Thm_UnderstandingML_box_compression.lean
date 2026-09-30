-- Prove2me | Theorems.Thm_UnderstandingML_box_compression
-- name    : UnderstandingML.box_compression
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T06:02:14.317899+00:00
-- url     : https://prove2.me/theorems/fb211c9c-2692-495c-ac0b-9d9e02751021
-- title:
--   §30.2.1: axis-aligned rectangles in ℝ^d have a compression scheme of size 2d (extremal positive examples per dimension, minimal enclosing rectangle)
-- statement:
--   **§30.2.1 (Axis Aligned Rectangles).** Consider the algorithm $A$ that works as follows: for each dimension, choose the two positive examples with extremal values at this dimension. Define $B$ to be the function that returns the minimal enclosing rectangle. Then, for $k = 2d$, we have that in the realizable case, $L_S(B(A(S))) = 0$.
--
--   Formally: the class of closed axis-aligned boxes in $\mathbb{R}^d$ has a compression scheme of size $2d$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §30.2.1 p. 412

import Definitions.Def_UnderstandingML_Compression

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **§30.2.1** (p. 412). The class of axis-aligned rectangles in `ℝ^d` has a compression scheme
of size `k = 2d`: for each dimension `A` selects the two positive examples with extremal values,
and `B` returns the minimal enclosing rectangle. -/
theorem box_compression (d : ℕ) : HasCompressionScheme (boxClass d) (2 * d) := by sorry

end UnderstandingML
