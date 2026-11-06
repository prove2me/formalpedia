-- Prove2me | Theorems.Thm_RH_Transport_TunedCandidate_all_subset_lengths_pos
-- name    : RH.Transport.TunedCandidate.all_subset_lengths_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:58:19.236246+00:00
-- url     : https://prove2.me/theorems/51e22ca2-1e95-4f03-abdd-206f8683b4ba
-- title:
--   Tuned Candidate: all subset lengths pos
-- statement:
--   The Tuned Candidate construction uses the all subset lengths pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedCandidate.lean#L261-L274
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedCandidate.lean#L261-L274

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem RH.Transport.TunedCandidate.all_subset_lengths_pos {d : ℝ} (hd : d ≤ ell) :
    0 < width - 2 * d ∧ 0 < lx - d ∧ 0 < ly - d ∧
      0 < ly - d - 11 * b / 6 := by sorry
