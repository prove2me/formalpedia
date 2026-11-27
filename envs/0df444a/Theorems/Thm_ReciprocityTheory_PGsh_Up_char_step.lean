-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_char_step
-- name    : ReciprocityTheory.PGsh.Up.char_step
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T18:29:57.113129+00:00
-- url     : https://prove2.me/theorems/be891f4e-1c03-4a4c-b5f9-358c05377b98
-- title:
--   Up: char step
-- statement:
--   The Up construction uses the char step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UpBrChar.lean#L71-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UpBrChar.lean#L71-L171

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

theorem ReciprocityTheory.PGsh.Up.char_step (hv : v.Integers R) {g N : ℕ} (M : Matrix (Fin g) (Fin N) R) (c : R) (hc : c ≠ 0)
    (hspan : ∀ s (hs : s ≤ g), ∀ w : Fin s → R, c • w ∈ omTr M s hs) (s : ℕ) (hs1 : s + 1 ≤ g)
    (ι : Fin s → Fin N)
    (hι : Submodule.span R (Set.range fun i : Fin s => fun a : Fin s =>
      M (Fin.castLE (Nat.le_of_succ_le hs1) a) (ι i)) = omTr M s (Nat.le_of_succ_le hs1)) :
    ∃ b, b ∉ Set.range ι ∧ Submodule.span R (Set.range fun i : Fin (s + 1) => fun a : Fin (s + 1) =>
      M (Fin.castLE hs1 a) (Fin.snoc (α := fun _ => Fin N) ι b i)) = omTr M (s + 1) hs1 := by sorry
