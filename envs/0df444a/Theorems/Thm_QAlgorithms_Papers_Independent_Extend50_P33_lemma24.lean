-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P33_lemma24
-- name    : QAlgorithms.Papers.Independent.Extend50.P33.lemma24
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:07:14.218663+00:00
-- url     : https://prove2.me/theorems/71a6eb86-edd3-4b1c-8c71-7e4c893a1e42
-- title:
--   Lemma 24: insertion of the last letter and cycle counts
-- statement:
--   Let $r\ge1$, $\rho\in S_{r-1}$, and $a\in\{1,\ldots,r\}$. Embed $\rho$ in $S_r$ fixing $r$, and put $\sigma=(a,r)\rho$, with $(r,r)=1$. Counting every fixed point as a cycle,
--
--   $$\ell(\sigma)=\begin{cases}\ell(\rho),&a
--   e r,\\\ell(\rho)+1,&a=r.\end{cases}$$
--
--   At $r=1$ only the identity case exists. This distinguishes insertion into an old cycle from adding a fixed point.
-- source:
--   Port-based teleportation in arbitrary dimension, arXiv:1612.09260v3, PDF p. 24, Lemma 24: insertion of the last letter and cycle counts

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P33

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted type constructors; local notation only reorders Word's arguments.

local notation "Word" => (fun d r : ℕ =>
  QAlgorithms.Papers.Independent.Information100.P58.Word r d)

local notation "Op" => (fun d r : ℕ =>
  QAlgorithms.Papers.Independent.Information100.P21.Op
    (QAlgorithms.Papers.Independent.Information100.P58.Word r d))

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

/-- PDF p.24 Lemma24: every insertion coset, including the identity and degree1. -/
theorem lemma24 (r : ℕ) (pi : Equiv.Perm (Fin r)) (a : Fin (r+1)) :
    cycles (Equiv.swap a (Fin.last r) * extendPerm pi) =
      cycles pi + (if a = Fin.last r then 1 else 0) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P33

end
