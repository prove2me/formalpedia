-- Prove2me | Theorems.Thm_P2M_GlobalTheory_RowLaw_GaugeDeriv_subst_zero__1393311a9232
-- name    : P2M_GlobalTheory_RowLaw_GaugeDeriv_subst_zero__1393311a9232
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-27T05:21:41.28981+00:00
-- url     : https://prove2.me/theorems/eff50a51-64d7-401c-aa14-26faadce81a3
-- title:
--   P2 M Global Theory Row Law Gauge Deriv subst zero  1393311a9232: P2 M Global Theory Row Law Gauge Deriv subst zero  1393311a9232
-- statement:
--   The P2 M Global Theory Row Law Gauge Deriv subst zero  1393311a9232 construction uses the P2 M Global Theory Row Law Gauge Deriv subst zero  1393311a9232 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugeDerivEqPairingOfIntegralGaugedLaw.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugeDerivEqPairingOfIntegralGaugedLaw.lean#L94-L96

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeDerivEqPairingOfIntegralGaugedLaw
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
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.GaugeDeriv
variable {C : Type} [Field C] {V : VF C} {σ τ υ : Type}

theorem P2M_GlobalTheory_RowLaw_GaugeDeriv_subst_zero__1393311a9232 [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0) :
    subst a (0 : MvPowerSeries σ C) = 0 := by sorry

alias «GlobalTheory».«RowLaw».«GaugeDeriv».«subst_zero'» := P2M_GlobalTheory_RowLaw_GaugeDeriv_subst_zero__1393311a9232
