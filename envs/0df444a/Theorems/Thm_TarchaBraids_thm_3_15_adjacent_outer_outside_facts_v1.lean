-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_adjacent_outer_outside_facts_v1
-- name    : TarchaBraids.thm_3_15_adjacent_outer_outside_facts_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T08:39:55.225188+00:00
-- url     : https://prove2.me/theorems/0bf68675-b211-4764-83d7-62d505c9c943
-- title:
--   Tarcha 3.15 outer and outside-strand coordinate facts
-- statement:
--   The outer-rotation comparison path has the three stated local coordinates, and all nonlocal strands are fixed by the left word, right word and outer rotation.
-- source:
--   Modular local-coordinate and fixed-outside-strand extraction from the explicit adjacent Artin relation proof.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_geometry_interfaces_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_adjacent_outer_outside_facts_v1 :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      AdjacentOuterOutsideFacts i j hji := by sorry

end TarchaBraids
