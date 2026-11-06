-- Prove2me | Theorems.Thm_RH_Transport_TunedCandidate_support_decay_absorbs_row_loss
-- name    : RH.Transport.TunedCandidate.support_decay_absorbs_row_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:58:34.92568+00:00
-- url     : https://prove2.me/theorems/be47a5ec-84f4-480e-a89a-3871a59ce99d
-- title:
--   Tuned Candidate: support decay absorbs row loss
-- statement:
--   The Tuned Candidate construction uses the support decay absorbs row loss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedCandidate.lean#L288-L293
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedCandidate.lean#L288-L293

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_SupportedMass_support_decay_absorbs_row_loss

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem RH.Transport.TunedCandidate.support_decay_absorbs_row_loss {d Z C mass : ℝ}
    (hd : 0 ≤ d) (hZ : 1 ≤ Z) (hC : 0 ≤ C)
    (hmass : mass ≤ C * Z ^ (-d / 2)) :
    mass * Z ^ (max 0 (5 * ell - 1 + d) / 8) ≤ C := by sorry
