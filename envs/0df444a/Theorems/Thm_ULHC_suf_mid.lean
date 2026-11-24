-- Prove2me | Theorems.Thm_ULHC_suf_mid
-- name    : ULHC.suf_mid
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:55:51.33379+00:00
-- url     : https://prove2.me/theorems/c329b636-bfa9-42ca-9ef1-ac6059493174
-- title:
--   ULHC: suf mid
-- statement:
--   The ULHC construction uses the suf mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearChain.lean#L121-L128
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearChain.lean#L121-L128

import Definitions.Def_ULHC_NearGeo
import Definitions.Def_ULHC_NearChain
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {z : StripSpec} {i i0 : ℕ}

theorem ULHC.suf_mid {p : Pt} (he : i % 2 = 0)
    (h : IsMid (suf z i).c (suf z i).s ((suf z i).n - 2) p) : IsMid z.c z.s (z.n - 2) p := by sorry
