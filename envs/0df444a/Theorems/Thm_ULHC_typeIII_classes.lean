-- Prove2me | Theorems.Thm_ULHC_typeIII_classes
-- name    : ULHC.typeIII_classes
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:43:32.411969+00:00
-- url     : https://prove2.me/theorems/a3701a2b-def6-4774-ab77-87706e9edd69
-- title:
--   ULHC: type III classes
-- statement:
--   The ULHC construction uses the type III classes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L545-L587
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L545-L587

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
include hF hT hk hcell hpat hsep

theorem ULHC.typeIII_classes (hγ : lat1 (cellJ c s (k + 2)) s ∈ F) {d : Pt} (hd : IsCell V d)
    {tf : Side} (hb : back d tf ∈ flipCol F c s (k + 2)) (hf : front d tf ∈ flipCol F c s (k + 2))
    (hl1 : lat1 d tf ∉ flipCol F c s (k + 2)) (hl2 : lat2 d tf ∉ flipCol F c s (k + 2))
    (hn : ¬ Conn (flipCol F c s (k + 2)) (back1 d tf) (front1 d tf)) :
    (Conn (flipCol F c s (k + 2)) (back1 d tf) (back1 (cellJ c s (k + 1)) s) ∧
        Conn (flipCol F c s (k + 2)) (front1 d tf) (front1 (cellJ c s (k + 1)) s)) ∨
      (Conn (flipCol F c s (k + 2)) (back1 d tf) (front1 (cellJ c s (k + 1)) s) ∧
        Conn (flipCol F c s (k + 2)) (front1 d tf) (back1 (cellJ c s (k + 1)) s)) := by sorry
