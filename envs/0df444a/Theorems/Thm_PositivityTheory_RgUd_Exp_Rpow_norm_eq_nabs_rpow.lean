-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_Exp_Rpow_norm_eq_nabs_rpow
-- name    : PositivityTheory.RgUd.Exp.Rpow.norm_eq_nabs_rpow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:50:02.152368+00:00
-- url     : https://prove2.me/theorems/4ee10296-0a40-4bd9-b074-b408e610ae9c
-- title:
--   Rpow: norm eq nabs rpow
-- statement:
--   The Rpow construction uses the norm eq nabs rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/GenericIrreducibility/GenericUnitary/NormEqOneOfValuationEqOne.lean#L70-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/GenericIrreducibility/GenericUnitary/NormEqOneOfValuationEqOne.lean#L70-L104

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

theorem PositivityTheory.RgUd.Exp.Rpow.norm_eq_nabs_rpow (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    ∃ s : ℝ, ∀ z : kˣ, ‖(χ z : ℂ)‖ = nabs k z ^ s := by sorry
