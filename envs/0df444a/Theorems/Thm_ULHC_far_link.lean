-- Prove2me | Theorems.Thm_ULHC_far_link
-- name    : ULHC.far_link
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:01:27.80051+00:00
-- url     : https://prove2.me/theorems/5d1494a3-c46d-4246-a1c3-c1523546c2c1
-- title:
--   ULHC: far link
-- statement:
--   The ULHC construction uses the far link property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Complete.lean#L267-L313
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Complete.lean#L267-L313

import Definitions.Def_ULHC_Reverse
import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
include hF hT hk hcell hpat hsep

theorem ULHC.far_link {d : Pt} {tf : Side} (hd : IsCell V d)
    (hb : back d tf ∈ flipCol F c s (k + 2)) (hf : front d tf ∈ flipCol F c s (k + 2))
    (hl1 : lat1 d tf ∉ flipCol F c s (k + 2)) (hl2 : lat2 d tf ∉ flipCol F c s (k + 2))
    (hn : ¬ Conn (flipCol F c s (k + 2)) (back1 d tf) (front1 d tf))
    (hfar : ∀ j < k + 2, ∀ x ∈ cellE d, x ∉ cellE (cellJ c s j)) :
    CR2 V F ⟨c, s, k + 2⟩ ⟨d, tf, 1⟩ := by sorry
