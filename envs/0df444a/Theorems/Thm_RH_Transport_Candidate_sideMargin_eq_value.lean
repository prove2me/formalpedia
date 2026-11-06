-- Prove2me | Theorems.Thm_RH_Transport_Candidate_sideMargin_eq_value
-- name    : RH.Transport.Candidate.sideMargin_eq_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:25:50.627202+00:00
-- url     : https://prove2.me/theorems/242332cc-91b3-4afa-a09e-0983ee2f832e
-- title:
--   Candidate: side Margin eq value
-- statement:
--   The Candidate construction uses the side Margin eq value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Candidate.lean#L122-L126
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Candidate.lean#L122-L126

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_Candidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section

theorem RH.Transport.Candidate.sideMargin_eq_value (term : SideCondition) :
    sideMargin term = sideMarginValue term := by sorry
