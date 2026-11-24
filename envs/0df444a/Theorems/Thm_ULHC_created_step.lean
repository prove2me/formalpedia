-- Prove2me | Theorems.Thm_ULHC_created_step
-- name    : ULHC.created_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:50:41.447427+00:00
-- url     : https://prove2.me/theorems/3edd7b26-6431-46d2-b8cc-cbf9155e06a9
-- title:
--   ULHC: created step
-- statement:
--   The ULHC construction uses the created step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Cr2.lean#L31-L44
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Cr2.lean#L31-L44

import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Cr2
import Theorems.Thm_ULHC_APair_flip

set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {G : Finset Edge} {c : Pt} {s : Side} {k : ℕ}

theorem ULHC.created_step (hk : k % 2 = 0) (hG : Deg2 V G)
    (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat G c s (k + 2))
    (hsep : ¬ Conn G (back1 c s) (front1 c s))
    (hsame : Conn G (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s))
    {x y : Pt} (hxy : Conn G x y) (hsplit : ¬ Conn (flip G (cellJ c s (k + 1))) x y)
    (hx : ¬ IsMid c s k x) (hy : ¬ IsMid c s k y) :
    ¬ Conn (flipCol G c s (k + 2)) x y := by sorry
