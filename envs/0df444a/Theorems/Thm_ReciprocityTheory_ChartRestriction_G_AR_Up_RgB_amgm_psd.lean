-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_RgB_amgm_psd
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.RgB.amgm_psd
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:03:13.782653+00:00
-- url     : https://prove2.me/theorems/4ea69f0d-c80d-5c05-a56d-30e88b3b1046
-- title:
--   Rg B: amgm psd
-- statement:
--   The Rg B construction uses the amgm psd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/RhGradStatementPfA.lean#L102-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/RhGradStatementPfA.lean#L102-L118

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.RgB
open Matrix
open scoped ComplexOrder Matrix
open ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.RgB.amgm_psd {m : ℕ} (hm : 0 < m) {P : Matrix (Fin m) (Fin m) ℂ} (hP : P.PosSemidef) :
    P.det.re ^ ((m : ℝ)⁻¹) ≤ P.trace.re / m := by sorry
