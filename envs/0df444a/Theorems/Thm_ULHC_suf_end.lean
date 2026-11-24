-- Prove2me | Theorems.Thm_ULHC_suf_end
-- name    : ULHC.suf_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:21:22.416651+00:00
-- url     : https://prove2.me/theorems/2bea369b-6541-4f6f-bc74-0c67a9f35908
-- title:
--   ULHC: suf end
-- statement:
--   The ULHC construction uses the suf end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearChain.lean#L99-L100
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearChain.lean#L99-L100

import Definitions.Def_ULHC_NearGeo
import Definitions.Def_ULHC_NearChain
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {z : StripSpec} {i i0 : ℕ}

theorem ULHC.suf_end (hi : i < z.n) : endCell (suf z i) = endCell z := by sorry
