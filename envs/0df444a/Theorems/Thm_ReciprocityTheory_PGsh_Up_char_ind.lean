-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_char_ind
-- name    : ReciprocityTheory.PGsh.Up.char_ind
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T18:27:15.660552+00:00
-- url     : https://prove2.me/theorems/1a83f3f1-bf26-57f7-b970-6b6fd9a77942
-- title:
--   Up: char ind
-- statement:
--   The Up construction uses the char ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UpBrChar.lean#L173-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UpBrChar.lean#L173-L217

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

theorem ReciprocityTheory.PGsh.Up.char_ind (hv : v.Integers R) {g N : ℕ} (M : Matrix (Fin g) (Fin N) R) (c : R) (hc : c ≠ 0)
    (hspan : ∀ s (hs : s ≤ g), ∀ w : Fin s → R, c • w ∈ omTr M s hs) :
    ∀ s (hs : s ≤ g), ∃ ι : Fin s → Fin N, Function.Injective ι ∧ ∀ s' (hs' : s' ≤ s),
      Submodule.span R (Set.range fun b : Fin s' => fun a : Fin s' =>
        M (Fin.castLE (hs'.trans hs) a) (ι (Fin.castLE hs' b))) = omTr M s' (hs'.trans hs) := by sorry
