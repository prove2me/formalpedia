-- Prove2me | Theorems.Thm_ULHC_strip_even_rel
-- name    : ULHC.strip_even_rel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:25:00.843113+00:00
-- url     : https://prove2.me/theorems/5c83775e-bcf8-4ea5-ba89-cc1c74af86fd
-- title:
--   ULHC: strip even rel
-- statement:
--   The ULHC construction uses the strip even rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/V2.lean#L65-L119
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/V2.lean#L65-L119

import Definitions.Def_ULHC_TheoremA
import Definitions.Def_ULHC_V2
import Theorems.Thm_ULHC_APair_flip

set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {c : Pt} {s : Side}

theorem ULHC.strip_even_rel (k : ℕ) (hk : k % 2 = 0) (F : Finset Edge) (hF : Deg2 V F)
    (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
    (hsep : ¬ Conn F (back1 c s) (front1 c s))
    (hsame : Conn F (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s)) :
    ∃ F1 : Finset Edge, F1 = flip F (cellJ c s (k + 1)) ∧
      flipCol F c s (k + 2) = flipCol F1 c s (k + 1) ∧
      ¬ Conn F1 (back1 (cellJ c s (k + 1)) s) (front1 (cellJ c s (k + 1)) s) ∧
      (∀ x y, Conn F1 x y → Conn F x y) ∧
      (∀ x y, Conn F x y ↔ Conn F1 x y ∨
        (Conn F1 x (back1 (cellJ c s (k + 1)) s) ∧ Conn F1 (front1 (cellJ c s (k + 1)) s) y) ∨
        (Conn F1 x (front1 (cellJ c s (k + 1)) s) ∧ Conn F1 (back1 (cellJ c s (k + 1)) s) y)) ∧
      ∀ x y, ¬ IsMid c s k x → ¬ IsMid c s k y →
        (Conn (flipCol F c s (k + 2)) x y ↔ Conn F1 x y ∨
          (Conn F1 x (back1 c s) ∧ Conn F1 (front1 c s) y) ∨
          (Conn F1 x (front1 c s) ∧ Conn F1 (back1 c s) y)) := by sorry
