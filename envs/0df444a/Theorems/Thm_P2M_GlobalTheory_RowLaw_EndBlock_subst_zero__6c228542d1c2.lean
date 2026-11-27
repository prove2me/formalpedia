-- Prove2me | Theorems.Thm_P2M_GlobalTheory_RowLaw_EndBlock_subst_zero__6c228542d1c2
-- name    : P2M_GlobalTheory_RowLaw_EndBlock_subst_zero__6c228542d1c2
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-27T06:06:56.580679+00:00
-- url     : https://prove2.me/theorems/f895de81-a102-427d-8b32-4a26af411900
-- title:
--   P2 M Global Theory Row Law End Block subst zero  6c228542d1c2: P2 M Global Theory Row Law End Block subst zero  6c228542d1c2
-- statement:
--   The P2 M Global Theory Row Law End Block subst zero  6c228542d1c2 construction uses the P2 M Global Theory Row Law End Block subst zero  6c228542d1c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugeAdjointEndPairElementaryBlock.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugeAdjointEndPairElementaryBlock.lean#L26-L28

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeAdjointEndPairElementaryBlock
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.EndBlock
open MvPowerSeries
variable {C : Type} [Field C]

theorem P2M_GlobalTheory_RowLaw_EndBlock_subst_zero__6c228542d1c2 {σ τ : Type} [Finite σ] {f : MvPowerSeries σ C} (hf : constantCoeff f = 0) :
    subst (fun _ : σ => (0 : MvPowerSeries τ C)) f = 0 := by sorry

alias «GlobalTheory».«RowLaw».«EndBlock».«subst_zero'» := P2M_GlobalTheory_RowLaw_EndBlock_subst_zero__6c228542d1c2
