-- Prove2me | Theorems.Thm_P2M_GlobalTheory_RowLaw_GoodPair_trace_ord__ef7abcbcab3e
-- name    : P2M_GlobalTheory_RowLaw_GoodPair_trace_ord__ef7abcbcab3e
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-27T06:00:00.38437+00:00
-- url     : https://prove2.me/theorems/06da6a57-85cf-5fbf-87ad-e862578acb0c
-- title:
--   P2 M Global Theory Row Law Good Pair trace ord  ef7abcbcab3e: P2 M Global Theory Row Law Good Pair trace ord  ef7abcbcab3e
-- statement:
--   The P2 M Global Theory Row Law Good Pair trace ord  ef7abcbcab3e construction uses the P2 M Global Theory Row Law Good Pair trace ord  ef7abcbcab3e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GoodCurvesPairingMemMaxIdeal.lean#L353-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GoodCurvesPairingMemMaxIdeal.lean#L353-L358

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AddCurveStableOfIntegralGaugedFormalGroupLaw
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AdjointEndPairMemGaugedCurveLogarithms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FrobeniusMemTypicalCurveSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GoodCurvesPairingMemMaxIdeal
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
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.RowLaw.CvEnd GlobalTheory.RowVal MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.GoodPair
variable {C : Type} [Field C]
variable {V : VF C}

theorem P2M_GlobalTheory_RowLaw_GoodPair_trace_ord__ef7abcbcab3e {l : ℕ} (hl : l.Prime) {ζ : C} (hζ : IsPrimitiveRoot ζ l) (k : Fin 2) {w : Fin 2 → ℕ} {n : ℕ}
    {F : MvPowerSeries (Fin 2) C} (hF : F ∈ ordGe C w n) :
    ∑ j ∈ Finset.range l, rescale (sc k (ζ ^ j)) F ∈ ordGe C w n := by sorry

alias «GlobalTheory».«RowLaw».«GoodPair».«trace_ord'» := P2M_GlobalTheory_RowLaw_GoodPair_trace_ord__ef7abcbcab3e
