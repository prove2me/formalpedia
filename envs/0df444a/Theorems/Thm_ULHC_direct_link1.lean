-- Prove2me | Theorems.Thm_ULHC_direct_link1
-- name    : ULHC.direct_link1
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:03:22.166073+00:00
-- url     : https://prove2.me/theorems/c51ae861-3884-4559-b89f-b21d9b2b901c
-- title:
--   ULHC: direct link1
-- statement:
--   The ULHC construction uses the direct link1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L637-L669
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L637-L669

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.direct_link1 {V : Finset Pt} {G : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
    (hk : k % 2 = 0) {σ τ : StripSpec} (hl : CR2 V G σ τ)
    (hσe : endCell σ = cellJ c s (k + 1)) (hd : τ.c = nb (cellJ c s (k + 1)) (latA s))
    (ht : τ.s = s ∨ (τ.s = s.opp ∧ τ.n = 1)) : CR2 V G ⟨c, s, k + 2⟩ τ := by sorry
