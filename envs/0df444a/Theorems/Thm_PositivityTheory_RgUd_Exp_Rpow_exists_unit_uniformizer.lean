-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_Exp_Rpow_exists_unit_uniformizer
-- name    : PositivityTheory.RgUd.Exp.Rpow.exists_unit_uniformizer
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:50:03.600548+00:00
-- url     : https://prove2.me/theorems/44ac2c0a-4456-4244-b215-55ea335ba7fc
-- title:
--   Rpow: exists unit uniformizer
-- statement:
--   The Rpow construction uses the exists unit uniformizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/GenericIrreducibility/GenericUnitary/NormEqOneOfValuationEqOne.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/GenericIrreducibility/GenericUnitary/NormEqOneOfValuationEqOne.lean#L15-L21

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
variable (k)

theorem PositivityTheory.RgUd.Exp.Rpow.exists_unit_uniformizer : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by sorry
