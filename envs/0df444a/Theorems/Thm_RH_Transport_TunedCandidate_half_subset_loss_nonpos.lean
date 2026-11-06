-- Prove2me | Theorems.Thm_RH_Transport_TunedCandidate_half_subset_loss_nonpos
-- name    : RH.Transport.TunedCandidate.half_subset_loss_nonpos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:58:26.624381+00:00
-- url     : https://prove2.me/theorems/382d146c-8831-4350-9299-a2a432906e4f
-- title:
--   Tuned Candidate: half subset loss nonpos
-- statement:
--   The Tuned Candidate construction uses the half subset loss nonpos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedCandidate.lean#L283-L286
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedCandidate.lean#L283-L286

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem RH.Transport.TunedCandidate.half_subset_loss_nonpos {d : ℝ} (hd : 0 ≤ d) :
    -d / 2 + max 0 (5 * ell - 1 + d) / 8 ≤ 0 := by sorry
