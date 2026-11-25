-- Prove2me | Theorems.Thm_P2M_GlobalTheory_StepData_Model_opE_ne_zero__77ad6a831e75
-- name    : P2M_GlobalTheory_StepData_Model_opE_ne_zero__77ad6a831e75
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:09:12.773679+00:00
-- url     : https://prove2.me/theorems/c753ca77-aee3-481f-b6b1-5e9d8f48a716
-- title:
--   P2 M Global Theory Step Data Model op E ne zero  77ad6a831e75: P2 M Global Theory Step Data Model op E ne zero  77ad6a831e75
-- statement:
--   The P2 M Global Theory Step Data Model op E ne zero  77ad6a831e75 construction uses the P2 M Global Theory Step Data Model op E ne zero  77ad6a831e75 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/TypeChainPrincipalEntryNeZero.lean#L62-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/TypeChainPrincipalEntryNeZero.lean#L62-L88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData GlobalTheory.StepData.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [MeasurableSpace k] [BorelSpace k]
omit [DecidableEq n] [DecidableEq n']

theorem P2M_GlobalTheory_StepData_Model_opE_ne_zero__77ad6a831e75 (ψ : AddChar k Circle) (ν : Measure k)
    [ν.IsAddHaarMeasure] (p : ℕ) {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hΦ : Φ ∈ SB _)
    (h01 : ∀ x, Φ x ≠ 0 → Φ x = ψ (ch x)) {x₀ : Matrix n n' k} {e₀} (he : Φ (affPt p x₀ e₀) ≠ 0) :
    opE ψ ν p Φ x₀ ≠ 0 := by sorry

alias «GlobalTheory».«StepData».«Model».«opE_ne_zero'» := P2M_GlobalTheory_StepData_Model_opE_ne_zero__77ad6a831e75
