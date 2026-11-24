-- Prove2me | Theorems.Thm_ULHC_inter_local
-- name    : ULHC.inter_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:42:27.778171+00:00
-- url     : https://prove2.me/theorems/06739ea8-9505-40aa-89fd-9f0063d2f154
-- title:
--   ULHC: inter local
-- statement:
--   The ULHC construction uses the inter local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L40-L50
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L40-L50

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_ACell_ab
import Theorems.Thm_ULHC_ACell_dk

set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.inter_local : ∀ (mb mt ml mr ab ad ak bd bk dk : Bool),
    triOK ab ad ak bd bk dk = true →
    -- dark sides join corners of one class
    (mb ≤ ab) → (mt ≤ dk) → (ml ≤ ad) → (mr ≤ bk) →
    -- no Type III cell
    ((mb && mt && !ml && !mr) ≤ ad) → ((ml && mr && !mb && !mt) ≤ ab) →
    -- an inter side has a dark neighbouring side
    ((!mb && !ab) ≤ (ml || mr)) → ((!mt && !dk) ≤ (ml || mr)) →
    ((!ml && !ad) ≤ (mb || mt)) → ((!mr && !bk) ≤ (mb || mt)) →
    (bI (!mb && !ab) + bI (!mt && !dk) + bI (!ml && !ad) + bI (!mr && !bk)) % 2 = 0 := by sorry
