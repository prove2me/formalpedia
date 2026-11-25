-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_hermC_orthonormal_coordinates
-- name    : ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.hermC_orthonormal_coordinates
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:19:21.647865+00:00
-- url     : https://prove2.me/theorems/69237ede-c0a1-413c-9122-6614dfb3df14
-- title:
--   Orthonormal Chart Bounds: herm C orthonormal coordinates
-- statement:
--   The Orthonormal Chart Bounds construction uses the herm C orthonormal coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermCOrthonormalCoordinates.lean#L89-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermCOrthonormalCoordinates.lean#L89-L109

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermCOrthonormalCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.hermC_orthonormal_coordinates {x : Frame X.Ψ r} (ho : X.IsOrtho x) (τ : X.Ψ) (p q : Fin r → ℂ) :
    hermC τ.1 X.Gm (mat x τ *ᵥ p) (mat x τ *ᵥ q) =
      mjip (mjpa X p) (mjpa X q) - mjip (mjpb X p) (mjpb X q) := by sorry
