-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SmGL_isSmooth_jac__a0d7e6d45b7a
-- name    : P2M_GlobalTheory_SmGL_isSmooth_jac__a0d7e6d45b7a
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:55.557244+00:00
-- url     : https://prove2.me/theorems/8a34c28e-d20c-4587-b040-4b402bb570f6
-- title:
--   P2 M Global Theory Sm GL is Smooth jac  a0d7e6d45b7a: P2 M Global Theory Sm GL is Smooth jac  a0d7e6d45b7a
-- statement:
--   The P2 M Global Theory Sm GL is Smooth jac  a0d7e6d45b7a construction uses the P2 M Global Theory Sm GL is Smooth jac  a0d7e6d45b7a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsSubquotientDetRepParInd.lean#L359-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsSubquotientDetRepParInd.lean#L359-L361

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL
open Matrix
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable {k}
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem P2M_GlobalTheory_SmGL_isSmooth_jac__a0d7e6d45b7a (e : a ⊕ b ≃ n) {π : Representation ℂ (GL n k) V} (hπ : IsSmooth π) :
    IsSmooth (jac₂ e π) := by sorry

alias «GlobalTheory».«SmGL».«isSmooth_jac₂» := P2M_GlobalTheory_SmGL_isSmooth_jac__a0d7e6d45b7a
