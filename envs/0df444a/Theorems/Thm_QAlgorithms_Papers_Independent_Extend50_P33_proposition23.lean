-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P33_proposition23
-- name    : QAlgorithms.Papers.Independent.Extend50.P33.proposition23
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:06:30.675541+00:00
-- url     : https://prove2.me/theorems/1054dc49-0ff8-4a8d-8d6d-ee9d4ea19d0c
-- title:
--   Proposition 23: multiplicity-square cycle-count formula
-- statement:
--   Let $d\ge2$ and $r\ge0$. Let $m_\nu$ be the actual multiplicities of the height-at-most-$d$ diagrams of size $r$ in the natural tensor permutation action. For $\sigma\in S_r$, let $\ell(\sigma)$ count all cycles, including fixed points. Then
--
--   $$\sum_{\nu\vdash r,\,h(\nu)\le d}m_\nu^2=\frac1{r!}\sum_{\sigma\in S_r}d^{2\ell(\sigma)}.$$
--
--   At degree zero both sides equal one. This identity evaluates the multiplicity normalization used in the optimal resource.
-- source:
--   Port-based teleportation in arbitrary dimension, arXiv:1612.09260v3, PDF p. 24, Proposition 23: multiplicity-square cycle-count formula

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

/-- PDF p.24 Proposition23 Eq.(84): fixed points count as cycles, including r=0. -/
theorem proposition23 (d r : ℕ) (hd : 2 ≤ d) :
    squareSum d r = (1/(r.factorial:ℝ)) *
      ∑ pi : Equiv.Perm (Fin r), (d:ℝ)^(2 * cycles pi) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P33

end
