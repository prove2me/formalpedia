-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhA_cross_psd
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA.cross_psd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:56:48.852032+00:00
-- url     : https://prove2.me/theorems/5187980d-62d1-41de-a5f9-a60f9bee4343
-- title:
--   Exh A: cross psd
-- statement:
--   The Exh A construction uses the cross psd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ExhaustStatementPfA.lean#L12-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ExhaustStatementPfA.lean#L12-L38

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LiftFactorization
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetMonoDetOneAdd
import Definitions.Def_Lemmata_PosDefOfRealQuadratic_QuadFormRealSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA
open Matrix
open scoped ComplexOrder Matrix
variable {p q : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA.cross_psd (Z W : Matrix (Fin p) (Fin q) ℂ) (hW : (1 - W * Wᴴ).PosDef) :
    ((1 - Z * Wᴴ) * (1 - W * Wᴴ)⁻¹ * (1 - Z * Wᴴ)ᴴ - (1 - Z * Zᴴ)).PosSemidef := by sorry
