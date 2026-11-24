-- Prove2me | Theorems.Thm_ULHC_link_of_F
-- name    : ULHC.link_of_F
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:08:20.641863+00:00
-- url     : https://prove2.me/theorems/51618770-3061-4beb-8999-5033215e5643
-- title:
--   ULHC: link of F
-- statement:
--   The ULHC construction uses the link of F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/PathComplete.lean#L358-L375
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/PathComplete.lean#L358-L375

import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_PathComplete
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge} {c : Pt} {d : Side} {k : ℕ}
  (hG : Deg2 V G) (hT : NoTypeIII V G) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c d j)) (hpat : StripPat G c d (k + 2))
  (hsep : ¬ Conn G (back1 c d) (front1 c d))
include hG hT hk hcell hpat hsep

theorem ULHC.link_of_F {q : StripSpec} (hq1 : 1 ≤ q.n)
    (hpatF : StripPat (flipCol G c d (k + 2)) q.c q.s q.n)
    (hcq : ∀ j < q.n, IsCell V (cellJ q.c q.s j)) (hso : SideOff ⟨c, d, k + 2⟩ q)
    (hne : ∀ j < q.n, cellJ q.c q.s j ≠ cellJ c d (k + 1))
    (hen : q.n % 2 = 0 → ∀ x ∈ cellE (endCell q), x ∉ cellE (cellJ c d (k + 1)))
    (hm1 : ¬ IsMid c d k (back1 q.c q.s)) (hm2 : ¬ IsMid c d k (front1 q.c q.s))
    (hcg : Conn G (back1 q.c q.s) (front1 q.c q.s))
    (hsepF : ¬ Conn (flipCol G c d (k + 2)) (back1 q.c q.s) (front1 q.c q.s)) :
    CR2 V G ⟨c, d, k + 2⟩ q := by sorry
