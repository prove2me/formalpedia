-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_l2NormSq_nonneg_gaussianTorus
-- name    : ReciprocityTheory.ChartRestriction.G.I2.l2NormSq_nonneg_gaussianTorus
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:55.214217+00:00
-- url     : https://prove2.me/theorems/accf99e2-7630-4b54-b790-3b655e0f72e5
-- title:
--   I2: l2 Norm Sq nonneg gaussian Torus
-- statement:
--   The I2 construction uses the l2 Norm Sq nonneg gaussian Torus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/L2NormSqNonnegGaussianTorus.lean#L51-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/L2NormSqNonnegGaussianTorus.lean#L51-L55

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfEqInner
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormSqNonnegGaussianTorus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.ChartRestriction.G.I2.l2NormSq_nonneg_gaussianTorus (X : PT E) (q : ℕ) {n : ℕ} (F : (Fin n → Vsp X.dim) → ℂ) : 0 ≤ X.l2 q F := by sorry
