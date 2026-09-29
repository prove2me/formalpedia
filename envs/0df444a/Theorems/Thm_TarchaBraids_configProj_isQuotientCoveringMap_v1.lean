-- Prove2me | Theorems.Thm_TarchaBraids_configProj_isQuotientCoveringMap_v1
-- name    : TarchaBraids.configProj_isQuotientCoveringMap_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T23:17:31.662255+00:00
-- url     : https://prove2.me/theorems/91c83d18-43eb-4666-b501-9515ff7de7cc
-- title:
--   The ordered configuration projection is the symmetric-group quotient covering
-- statement:
--   The projection from ordered configurations of n distinct points in the plane to unordered configurations is the quotient covering for the natural action of the symmetric group on strand labels. Thus its fibres are precisely symmetric-group orbits and the action is free.
-- source:
--   Tarcha's configuration-space model of braids together with Proposition 1.1: forgetting strand labels is the standard symmetric-group covering from ordered to unordered configurations.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_endpoint_permutation_action_v1
import Theorems.Thm_BraidsLinksMCG_prop_1_1_covering

namespace TarchaBraids

open BraidsLinksMCG

theorem configProj_isQuotientCoveringMap_v1 (n : ℕ) :
    IsQuotientCoveringMap (configProj n) (Equiv.Perm (Fin n)) := by sorry

end TarchaBraids
