-- Prove2me | Theorems.Thm_ULHC_direct_link2
-- name    : ULHC.direct_link2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:03:28.799639+00:00
-- url     : https://prove2.me/theorems/6fcb0303-b485-4de8-9dc2-51dc04a1120f
-- title:
--   ULHC: direct link2
-- statement:
--   The ULHC construction uses the direct link2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L674-L706
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L674-L706

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.direct_link2 {V : Finset Pt} {G : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
    (hk : k % 2 = 0) {σ τ : StripSpec} (hl : CR2 V G σ τ)
    (hσe : endCell σ = cellJ c s (k + 1)) (hd : τ.c = nb (cellJ c s (k + 1)) (latB s))
    (ht : τ.s = s ∨ (τ.s = s.opp ∧ τ.n = 1)) : CR2 V G ⟨c, s, k + 2⟩ τ := by sorry
