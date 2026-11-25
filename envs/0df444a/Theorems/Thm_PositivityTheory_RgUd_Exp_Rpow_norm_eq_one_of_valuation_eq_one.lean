-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_Exp_Rpow_norm_eq_one_of_valuation_eq_one
-- name    : PositivityTheory.RgUd.Exp.Rpow.norm_eq_one_of_valuation_eq_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:50:02.225153+00:00
-- url     : https://prove2.me/theorems/6700d484-be84-4d81-87e2-da51dfa449c1
-- title:
--   Rpow: norm eq one of valuation eq one
-- statement:
--   The Rpow construction uses the norm eq one of valuation eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/GenericIrreducibility/GenericUnitary/NormEqOneOfValuationEqOne.lean#L50-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/GenericIrreducibility/GenericUnitary/NormEqOneOfValuationEqOne.lean#L50-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_GenericIrreducibility_GenericUnitary_NormEqOneOfValuationEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.Exp PositivityTheory.RgUd.Exp.Rpow
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem PositivityTheory.RgUd.Exp.Rpow.norm_eq_one_of_valuation_eq_one (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) {u : kˣ}
    (hu : valuation k (u : k) = 1) : ‖(χ u : ℂ)‖ = 1 := by sorry
