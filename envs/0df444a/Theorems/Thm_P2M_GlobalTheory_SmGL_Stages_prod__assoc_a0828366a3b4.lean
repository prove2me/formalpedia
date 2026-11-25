-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SmGL_Stages_prod__assoc_a0828366a3b4
-- name    : P2M_GlobalTheory_SmGL_Stages_prod__assoc_a0828366a3b4
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:09:27.535625+00:00
-- url     : https://prove2.me/theorems/194d579f-7f6a-48e1-97b0-fcc5415ad27f
-- title:
--   P2 M Global Theory Sm GL Stages prod  assoc a0828366a3b4: P2 M Global Theory Sm GL Stages prod  assoc a0828366a3b4
-- statement:
--   The P2 M Global Theory Sm GL Stages prod  assoc a0828366a3b4 construction uses the P2 M Global Theory Sm GL Stages prod  assoc a0828366a3b4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyInv.lean#L419-L423
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyInv.lean#L419-L423

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Topology Filter
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.Stages

theorem P2M_GlobalTheory_SmGL_Stages_prod__assoc_a0828366a3b4 : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r s t : ℕ) (V₁ V₂ V₃ : Type) [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃] (π₁ : Representation ℂ (GL (Fin r) k) V₁) (π₂ : Representation ℂ (GL (Fin s) k) V₂) (π₃ : Representation ℂ (GL (Fin t) k) V₃), IsSmooth π₁ → IsSmooth π₂ → IsSmooth π₃ → Nonempty ((prod₂ (prod₂ π₁ π₂) π₃).Equiv (ind₂ (stdSum (Nat.add_assoc r s t).symm) (extTensor π₁ (prod₂ π₂ π₃)))) := by sorry

alias «GlobalTheory».«SmGL».«Stages».«prod₂_assoc» := P2M_GlobalTheory_SmGL_Stages_prod__assoc_a0828366a3b4
