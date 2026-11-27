-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_char_len
-- name    : ReciprocityTheory.PGsh.Up.char_len
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T18:27:16.64315+00:00
-- url     : https://prove2.me/theorems/78415bbe-cad8-5342-a748-3eee0b98500e
-- title:
--   Up: char len
-- statement:
--   The Up construction uses the char len property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UpBrChar.lean#L225-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UpBrChar.lean#L225-L237

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
variable {C : Type} [Field C] {v : Valuation C NNReal} [Algebra R C]

theorem ReciprocityTheory.PGsh.Up.char_len (hv : v.Integers R) {g N : ℕ} (M : Matrix (Fin g) (Fin N) R) (ι : Fin g → Fin N)
    (s : ℕ) (hs : s ≤ g)
    (hι : Submodule.span R (Set.range fun b : Fin s => fun a : Fin s =>
      M (Fin.castLE hs a) (ι (Fin.castLE hs b))) = omTr M s hs) :
    HasLen v R ((Fin s → R) ⧸ omTr M s hs)
      (v (algebraMap R C (Matrix.of fun a b : Fin s => M (Fin.castLE hs a) (ι (Fin.castLE hs b))).det)) := by sorry
