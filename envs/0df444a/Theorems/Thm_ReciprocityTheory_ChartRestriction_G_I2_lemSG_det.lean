-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_lemSG_det
-- name    : ReciprocityTheory.ChartRestriction.G.I2.lemSG_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:08.393703+00:00
-- url     : https://prove2.me/theorems/1fedfedc-b5d4-4d72-8c26-b0f05af171c1
-- title:
--   I2: lem SG det
-- statement:
--   The I2 construction uses the lem SG det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaSA.lean#L55-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaSA.lean#L55-L82

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
open scoped Matrix
noncomputable section
variable {ι : Type} [Fintype ι]

theorem ReciprocityTheory.ChartRestriction.G.I2.lemSG_det {n : ℕ} (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℂ ι))
    (b₀ : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℂ ι)) :
    (lemSG b).det = LinearMap.det (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) *
      b₀.toBasis.det b * b₀.toBasis.det b := by sorry
