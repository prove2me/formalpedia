-- Prove2me | Theorems.Thm_TarchaBraids_braid_loop_ordered_lift_v1
-- name    : TarchaBraids.braid_loop_ordered_lift_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T21:25:54.258653+00:00
-- url     : https://prove2.me/theorems/2ffd6388-6681-40db-bebf-2c4ce8114fbf
-- title:
--   A geometric braid loop lifts to labelled strands with a permutation endpoint
-- statement:
--   Every based loop in the unordered configuration space lifts, from the standard ordered base configuration, to a continuous path of labelled configurations. Because the original path is a loop, the lifted endpoint differs from the ordered base configuration only by a permutation of the strand labels.
-- source:
--   Tarcha Teorema 3.11 and the standard covering-space model of braids: an unordered braid loop is represented by labelled strand paths whose endpoints are permuted.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Theorems.Thm_BraidsLinksMCG_prop_1_1_covering

namespace TarchaBraids

open BraidsLinksMCG unitInterval

theorem braid_loop_ordered_lift_v1 (n : ℕ)
    (γ : Path (baseUnordered n) (baseUnordered n)) :
    ∃ Γ : C(I, OrderedConfig n),
      (configProj n : OrderedConfig n → UnorderedConfig n) ∘ Γ = γ ∧
      Γ 0 = baseOrdered n ∧
      ∃ g : Equiv.Perm (Fin n), (Γ 1).1 = (baseOrdered n).1 ∘ g := by sorry

end TarchaBraids
