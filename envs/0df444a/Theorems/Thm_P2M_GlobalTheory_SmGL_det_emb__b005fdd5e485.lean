-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SmGL_det_emb__b005fdd5e485
-- name    : P2M_GlobalTheory_SmGL_det_emb__b005fdd5e485
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:36:54.384953+00:00
-- url     : https://prove2.me/theorems/825c9e06-8020-4dd1-9c7e-0f3cb65790db
-- title:
--   P2 M Global Theory Sm GL det emb  b005fdd5e485: P2 M Global Theory Sm GL det emb  b005fdd5e485
-- statement:
--   The P2 M Global Theory Sm GL det emb  b005fdd5e485 construction uses the P2 M Global Theory Sm GL det emb  b005fdd5e485 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L617-L622
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L617-L622

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SmGL
open Matrix
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable {R}
variable (R)
variable {R}
variable (R)
variable {a b : Type}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
open Matrix
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable {R}
variable (R)
variable {R}
variable (R)
variable {a b : Type}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem P2M_GlobalTheory_SmGL_det_emb__b005fdd5e485 (e : a ⊕ b ≃ n) (g : GL a R × GL b R) :
    GeneralLinearGroup.det (_root_.GlobalTheory.SmGL.emb₂ R e g) =
      GeneralLinearGroup.det g.1 * GeneralLinearGroup.det g.2 := by sorry

alias «GlobalTheory».«SmGL».«det_emb₂» := P2M_GlobalTheory_SmGL_det_emb__b005fdd5e485
