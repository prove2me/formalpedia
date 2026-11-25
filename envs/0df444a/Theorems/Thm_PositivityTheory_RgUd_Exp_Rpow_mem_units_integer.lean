-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_Exp_Rpow_mem_units_integer
-- name    : PositivityTheory.RgUd.Exp.Rpow.mem_units_integer
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:49:50.629615+00:00
-- url     : https://prove2.me/theorems/34b6cf96-679d-5c17-a629-98b35d4c0e3c
-- title:
--   Rpow: mem units integer
-- statement:
--   The Rpow construction uses the mem units integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/GenericIrreducibility/GenericUnitary/NormEqOneOfValuationEqOne.lean#L42-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/GenericIrreducibility/GenericUnitary/NormEqOneOfValuationEqOne.lean#L42-L48

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
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem PositivityTheory.RgUd.Exp.Rpow.mem_units_integer {u : kˣ} (hu : valuation k (u : k) = 1) :
    u ∈ (𝒪[k]).toSubmonoid.units := by sorry
