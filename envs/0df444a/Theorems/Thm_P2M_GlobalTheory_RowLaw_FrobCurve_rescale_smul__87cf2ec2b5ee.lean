-- Prove2me | Theorems.Thm_P2M_GlobalTheory_RowLaw_FrobCurve_rescale_smul__87cf2ec2b5ee
-- name    : P2M_GlobalTheory_RowLaw_FrobCurve_rescale_smul__87cf2ec2b5ee
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T05:52:41.841697+00:00
-- url     : https://prove2.me/theorems/e107f982-4b2f-4d73-9f14-ff5376abda1e
-- title:
--   P2 M Global Theory Row Law Frob Curve rescale smul  87cf2ec2b5ee: P2 M Global Theory Row Law Frob Curve rescale smul  87cf2ec2b5ee
-- statement:
--   The P2 M Global Theory Row Law Frob Curve rescale smul  87cf2ec2b5ee construction uses the P2 M Global Theory Row Law Frob Curve rescale smul  87cf2ec2b5ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FrobeniusMemTypicalCurveSet.lean#L59-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FrobeniusMemTypicalCurveSet.lean#L59-L63

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedFormalGroupCurveLogarithmsAddSubgroupRescaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemCvOfSubstXPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FrobeniusMemTypicalCurveSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.FrobCurve
variable {C : Type} [Field C]

theorem P2M_GlobalTheory_RowLaw_FrobCurve_rescale_smul__87cf2ec2b5ee (s c : C) (f : PowerSeries C) :
    PowerSeries.rescale s (c • f) = c • PowerSeries.rescale s f := by sorry

alias «GlobalTheory».«RowLaw».«FrobCurve».«rescale_smul'» := P2M_GlobalTheory_RowLaw_FrobCurve_rescale_smul__87cf2ec2b5ee
