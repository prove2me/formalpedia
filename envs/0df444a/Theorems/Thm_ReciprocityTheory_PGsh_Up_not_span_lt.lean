-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_not_span_lt
-- name    : ReciprocityTheory.PGsh.Up.not_span_lt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T04:36:43.152102+00:00
-- url     : https://prove2.me/theorems/51c25983-03bc-5a28-a2a4-acda0b6b29cf
-- title:
--   Up: not span lt
-- statement:
--   The Up construction uses the not span lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UpBrChar.lean#L44-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UpBrChar.lean#L44-L60

import Definitions.Def_ReciprocityTheory_DualLattices_DetIntegralNonneg
import Definitions.Def_ReciprocityTheory_DualLattices_UpBrChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {R : Type} [CommRing R] [IsDomain R]

theorem ReciprocityTheory.PGsh.Up.not_span_lt {s : ℕ} (B : Matrix (Fin (s + 1)) (Fin s) R) (c : R) (hc : c ≠ 0)
    (h : ∀ w : Fin (s + 1) → R, c • w ∈ Submodule.span R (Set.range fun i => fun a => B a i)) :
    False := by sorry
