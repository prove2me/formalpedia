-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SmGL_isSmooth_jac_Lower_22dc1bd467cd
-- name    : P2M_GlobalTheory_SmGL_isSmooth_jac_Lower_22dc1bd467cd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:08:00.680809+00:00
-- url     : https://prove2.me/theorems/72db2905-d0c4-4d37-8db4-64e27d46f8fe
-- title:
--   P2 M Global Theory Sm GL is Smooth jac Lower 22dc1bd467cd: P2 M Global Theory Sm GL is Smooth jac Lower 22dc1bd467cd
-- statement:
--   The P2 M Global Theory Sm GL is Smooth jac Lower 22dc1bd467cd construction uses the P2 M Global Theory Sm GL is Smooth jac Lower 22dc1bd467cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsSubquotientDetRepParInd.lean#L363-L365
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsSubquotientDetRepParInd.lean#L363-L365

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

theorem P2M_GlobalTheory_SmGL_isSmooth_jac_Lower_22dc1bd467cd (e : a ⊕ b ≃ n) {π : Representation ℂ (GL n k) V} (hπ : IsSmooth π) :
    IsSmooth (jac₂Lower e π) := by sorry

alias «GlobalTheory».«SmGL».«isSmooth_jac₂Lower» := P2M_GlobalTheory_SmGL_isSmooth_jac_Lower_22dc1bd467cd
