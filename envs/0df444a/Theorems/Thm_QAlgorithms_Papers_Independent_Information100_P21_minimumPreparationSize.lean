-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_minimumPreparationSize
-- name    : QAlgorithms.Papers.Independent.Information100.P21.minimumPreparationSize
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:56:38.444903+00:00
-- url     : https://prove2.me/theorems/c652bb3d-4b67-4366-95c5-5dfb5a77dc8b
-- title:
--   VI.17 — Proposition VI.17 (Minimum pure-product preparation size for X states). In√the entangled w-branch, the minimum
-- statement:
--   Among all separable optimal noises and all their pure-product convex decompositions for a physical X state in the entangled $w$ branch, put $t=w$. The minimum number of nonzero terms is
--   $$\begin{cases}1,&\sqrt{bc}<t\le\max(b,c),\\2,&t>\max(b,c).\end{cases}$$
--   The $z$ branch follows by replacing $(b,c,w)$ by $(a,d,z)$. The minimization includes nondiagonal optimal noises and includes the one-term internal boundary.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 20, VI.17 — Proposition VI.17 (Minimum pure-product preparation size for X states). In√the entangled w-branch, the minimum

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 20, Proposition VI.17 (Minimum pure-product preparation size for X states). In√the entangled w-branch, the minimum. -/
theorem minimumPreparationSize (a b c d w z : ℝ) (h : physicalX a b c d w z) :
  (b*c<w^2 → IsLeast (preparationSizes (xstate a b c d w z)) (if w ≤ max b c then 1 else 2)) ∧
  (a*d<z^2 → IsLeast (preparationSizes (xstate a b c d w z)) (if z ≤ max a d then 1 else 2)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
