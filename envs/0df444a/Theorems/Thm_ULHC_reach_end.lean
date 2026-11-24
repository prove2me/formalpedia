-- Prove2me | Theorems.Thm_ULHC_reach_end
-- name    : ULHC.reach_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:34:08.416265+00:00
-- url     : https://prove2.me/theorems/f4319ab1-65b1-4e50-99ac-774575d94911
-- title:
--   ULHC: reach end
-- statement:
--   The ULHC construction uses the reach end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearChain.lean#L42-L52
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearChain.lean#L42-L52

import Definitions.Def_ULHC_NearGeo
import Definitions.Def_ULHC_NearChain
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  {z : Pt} {tf : Side} {m i0 : ℕ} (hz : SigFrom F z tf m i0)
include hk hpat hz

theorem ULHC.reach_end : ∀ d i j, j + d = k + 1 → i0 ≤ i → i < m → cellJ z tf i = cellJ c s j →
    ∃ i', i ≤ i' ∧ i' < m ∧ cellJ z tf i' = cellJ c s (k + 1) := by sorry
