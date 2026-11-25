-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_RgB_amgm
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.RgB.amgm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:31:02.196843+00:00
-- url     : https://prove2.me/theorems/0ad6e756-dbf3-48b7-a4b4-0a5fbf772f9e
-- title:
--   Rg B: amgm
-- statement:
--   The Rg B construction uses the amgm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/RhGradStatementPfA.lean#L120-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/RhGradStatementPfA.lean#L120-L142

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.RgB.amgm {m : ℕ} (hm : 0 < m) {A A0 : Matrix (Fin m) (Fin m) ℂ} (hA : A.PosDef)
    (hA0 : A0.PosDef) :
    A.det.re ^ ((m : ℝ)⁻¹) ≤ A0.det.re ^ ((m : ℝ)⁻¹) * ((A * A0⁻¹).trace.re / m) := by sorry
