-- Prove2me | Theorems.Thm_RH_Transport_TunedCandidate_half_subset_loss_le
-- name    : RH.Transport.TunedCandidate.half_subset_loss_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:27:01.866197+00:00
-- url     : https://prove2.me/theorems/f3e13309-a419-4be9-a29a-43a0c1b30889
-- title:
--   Tuned Candidate: half subset loss le
-- statement:
--   The supported-mass decay absorbs the square-root reflected row loss.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedCandidate.lean#L277-L281
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedCandidate.lean#L277-L281

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem RH.Transport.TunedCandidate.half_subset_loss_le {d : ℝ} (hd : 0 ≤ d) :
    -d / 2 + max 0 (5 * ell - 1 + d) / 8 ≤ -3 * d / 8 := by sorry
