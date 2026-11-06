-- Prove2me | Theorems.Thm_RH_Transport_Candidate_subset_loss_nonpos
-- name    : RH.Transport.Candidate.subset_loss_nonpos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:59:34.414597+00:00
-- url     : https://prove2.me/theorems/dfaad817-770f-4471-b8c1-111ac9faba1b
-- title:
--   Candidate: subset loss nonpos
-- statement:
--   The Candidate construction uses the subset loss nonpos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Candidate.lean#L161-L163
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Candidate.lean#L161-L163

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_Candidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section

theorem RH.Transport.Candidate.subset_loss_nonpos {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ ell p) :
    subsetLoss p d ≤ 0 := by sorry
