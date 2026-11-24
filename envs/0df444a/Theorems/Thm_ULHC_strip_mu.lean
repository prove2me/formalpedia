-- Prove2me | Theorems.Thm_ULHC_strip_mu
-- name    : ULHC.strip_mu
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:41:52.081953+00:00
-- url     : https://prove2.me/theorems/d1e5063a-69b2-493e-80a4-2475c39402fc
-- title:
--   ULHC: strip mu
-- statement:
--   The ULHC construction uses the strip mu property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Phase2.lean#L143-L175
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Phase2.lean#L143-L175

import Definitions.Def_ULHC_Phase
import Definitions.Def_ULHC_Phase2
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.strip_mu {V : Finset Pt} {F H : Finset Edge} {c : Pt} {s : Side} {o : Bool}
    (hp : ParOK c s o) :
    ∀ n, StripPat F c s n → (∀ j < n, IsCell V (cellJ c s j)) →
      (∀ j < n, Good o (D F H (cellJ c s j))) →
      mu V (flipCol F c s n) H + 2 * n = mu V F H := by sorry
