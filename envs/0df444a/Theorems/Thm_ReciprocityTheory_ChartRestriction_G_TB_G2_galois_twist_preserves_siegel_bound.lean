-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_galois_twist_preserves_siegel_bound
-- name    : ReciprocityTheory.ChartRestriction.G.TB.G2.galois_twist_preserves_siegel_bound
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:39:59.751402+00:00
-- url     : https://prove2.me/theorems/e1d9d3d2-fdc0-5d19-bfa5-55c38d89079b
-- title:
--   G2: galois twist preserves siegel bound
-- statement:
--   The G2 construction uses the galois twist preserves siegel bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/G2Assumption.lean#L11-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/G2Assumption.lean#L11-L52

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_G2Assumption
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.G2

theorem ReciprocityTheory.ChartRestriction.G.TB.G2.galois_twist_preserves_siegel_bound (hA : ExpAddZeroConstant) (hE : ConstantCoeffSubstitution) (hG : CanonicalGaugeDiffBiadditive) (hQ : QuadraticFormDerivatives)
    (hW : WickOperatorVanishing) : AdmissibilitySecond := by sorry
