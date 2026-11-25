-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_polyDeriv_smul_fun
-- name    : ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_smul_fun
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:30:13.976353+00:00
-- url     : https://prove2.me/theorems/4ffde34b-fbf4-43bd-a6ce-a414cc3d1fd9
-- title:
--   I2: poly Deriv smul fun
-- statement:
--   The I2 construction uses the poly Deriv smul fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/L2NormFundamentalDomain.lean#L222-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/L2NormFundamentalDomain.lean#L222-L232

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
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
noncomputable section
variable {E : Type} [Field E] [NumberField E] (X : PT E)

theorem ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_smul_fun {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (P : MvPolynomial σ ℂ) (u : σ → W) {F : W → ℂ} (hF : ContDiff ℂ (⊤ : ℕ∞) F) (c : ℂ) (x : W) :
    polyDeriv P u (c • F) x = c * polyDeriv P u F x := by sorry
