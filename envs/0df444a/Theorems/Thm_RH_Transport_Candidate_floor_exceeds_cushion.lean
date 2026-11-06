-- Prove2me | Theorems.Thm_RH_Transport_Candidate_floor_exceeds_cushion
-- name    : RH.Transport.Candidate.floor_exceeds_cushion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:59:25.305216+00:00
-- url     : https://prove2.me/theorems/1792b77c-a8a7-44a1-a9a6-05e4b06b5e5d
-- title:
--   Candidate: floor exceeds cushion
-- statement:
--   The Candidate construction uses the floor exceeds cushion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Candidate.lean#L133-L135
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Candidate.lean#L133-L135

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_Candidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section

theorem RH.Transport.Candidate.floor_exceeds_cushion :
    cushion - 2 * zeta < sideMargin .floor - 2 * zeta := by sorry
