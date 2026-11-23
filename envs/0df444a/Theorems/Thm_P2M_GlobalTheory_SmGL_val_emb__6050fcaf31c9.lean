-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SmGL_val_emb__6050fcaf31c9
-- name    : P2M_GlobalTheory_SmGL_val_emb__6050fcaf31c9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:45.415715+00:00
-- url     : https://prove2.me/theorems/8d4dc8fa-2b36-4bb6-9636-f340c154eecd
-- title:
--   P2 M Global Theory Sm GL val emb  6050fcaf31c9: P2 M Global Theory Sm GL val emb  6050fcaf31c9
-- statement:
--   The P2 M Global Theory Sm GL val emb  6050fcaf31c9 construction uses the P2 M Global Theory Sm GL val emb  6050fcaf31c9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L590-L605
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/LeviEmbMemNormalizerLower.lean#L590-L605

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

theorem P2M_GlobalTheory_SmGL_val_emb__6050fcaf31c9 (e : a ⊕ b ≃ n) (g : GL a R × GL b R) :
    (_root_.GlobalTheory.SmGL.emb₂ R e g : Matrix n n R) =
      Matrix.reindex e e (fromBlocks g.1.val 0 0 g.2.val) := by sorry

alias «GlobalTheory».«SmGL».«val_emb₂» := P2M_GlobalTheory_SmGL_val_emb__6050fcaf31c9
