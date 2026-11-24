-- Prove2me | Theorems.Thm_ULHC_suf_valid
-- name    : ULHC.suf_valid
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:34:35.451806+00:00
-- url     : https://prove2.me/theorems/49865bc1-7610-4ebd-a8b4-24358f6b774b
-- title:
--   ULHC: suf valid
-- statement:
--   The ULHC construction uses the suf valid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearChain.lean#L142-L146
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearChain.lean#L142-L146

import Definitions.Def_ULHC_NearGeo
import Definitions.Def_ULHC_NearChain
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {z : StripSpec} {i i0 : ℕ}

theorem ULHC.suf_valid (hp : StripPat F z.c z.s z.n) (hc : ∀ j < z.n, IsCell V (cellJ z.c z.s j))
    (he : i % 2 = 0) (hi : i < z.n)
    (hsep : ¬ Conn F (back1 (cellJ z.c z.s i) z.s) (front1 (cellJ z.c z.s i) z.s)) :
    ValidStrip V F (suf z i) := by sorry
