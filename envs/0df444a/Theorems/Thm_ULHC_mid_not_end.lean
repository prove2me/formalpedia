-- Prove2me | Theorems.Thm_ULHC_mid_not_end
-- name    : ULHC.mid_not_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:43:37.249721+00:00
-- url     : https://prove2.me/theorems/979a14da-df21-4c3e-94cb-e09c195fb61a
-- title:
--   ULHC: mid not end
-- statement:
--   The ULHC construction uses the mid not end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L477-L539
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L477-L539

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
include hF hk hcell hpat

theorem ULHC.mid_not_end (_hγ : lat1 (cellJ c s (k + 2)) s ∈ F) {d : Pt} {e : Edge} {z : Pt}
    (hz : IsMid c s k z) (he : e ∈ flipCol F c s (k + 2)) (hez : e.p = z ∨ e.q = z)
    (hed : e ∈ cellE d) : NotTypeIII V (flipCol F c s (k + 2)) d := by sorry
