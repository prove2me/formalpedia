-- Prove2me | Theorems.Thm_RH_Transport_TunedCandidate_floor_exceeds_cushion
-- name    : RH.Transport.TunedCandidate.floor_exceeds_cushion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:58:09.989945+00:00
-- url     : https://prove2.me/theorems/ac537686-1873-47d1-896d-c043bd7d3cdd
-- title:
--   Tuned Candidate: floor exceeds cushion
-- statement:
--   The Tuned Candidate construction uses the floor exceeds cushion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedCandidate.lean#L226-L228
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedCandidate.lean#L226-L228

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem RH.Transport.TunedCandidate.floor_exceeds_cushion : cushion < sideMargin .floor := by sorry
