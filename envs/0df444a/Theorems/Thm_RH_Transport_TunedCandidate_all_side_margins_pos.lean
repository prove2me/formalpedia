-- Prove2me | Theorems.Thm_RH_Transport_TunedCandidate_all_side_margins_pos
-- name    : RH.Transport.TunedCandidate.all_side_margins_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:26:26.847197+00:00
-- url     : https://prove2.me/theorems/4bb8a3ca-4498-49cd-abfe-4c2ecdf85ba5
-- title:
--   Tuned Candidate: all side margins pos
-- statement:
--   The Tuned Candidate construction uses the all side margins pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedCandidate.lean#L222-L224
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedCandidate.lean#L222-L224

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem RH.Transport.TunedCandidate.all_side_margins_pos (term : SideCondition) : 0 < sideMargin term := by sorry
