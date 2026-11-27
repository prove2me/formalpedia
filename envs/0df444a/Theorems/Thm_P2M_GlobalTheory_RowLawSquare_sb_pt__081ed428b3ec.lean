-- Prove2me | Theorems.Thm_P2M_GlobalTheory_RowLawSquare_sb_pt__081ed428b3ec
-- name    : P2M_GlobalTheory_RowLawSquare_sb_pt__081ed428b3ec
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T05:14:57.881346+00:00
-- url     : https://prove2.me/theorems/86eb4779-3f58-54f3-b6b0-80882261041c
-- title:
--   P2 M Global Theory Row Law Square sb pt  081ed428b3ec: P2 M Global Theory Row Law Square sb pt  081ed428b3ec
-- statement:
--   The P2 M Global Theory Row Law Square sb pt  081ed428b3ec construction uses the P2 M Global Theory Row Law Square sb pt  081ed428b3ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IsIntegralGaugedFormalGroupLawSelfConjugateSquar.lean#L163-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IsIntegralGaugedFormalGroupLawSelfConjugateSquar.lean#L163-L164

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IsIntegralGaugedFormalGroupLawSelfConjugateSquar
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
open scoped BigOperators
open MvPowerSeries Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.RowLawSquare
variable {C : Type} [Field C] {σ τ : Type}
variable {dd : ℕ}

theorem P2M_GlobalTheory_RowLawSquare_sb_pt__081ed428b3ec {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (ha : ∀ j, Zc (a j)) (j : Fin n) :
    (fun i => sb a (pt C dd j i)) = a j := by sorry

alias «GlobalTheory».«RowLawSquare».«sb_pt'» := P2M_GlobalTheory_RowLawSquare_sb_pt__081ed428b3ec
