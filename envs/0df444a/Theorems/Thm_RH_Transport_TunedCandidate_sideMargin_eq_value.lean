-- Prove2me | Theorems.Thm_RH_Transport_TunedCandidate_sideMargin_eq_value
-- name    : RH.Transport.TunedCandidate.sideMargin_eq_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:26:25.199509+00:00
-- url     : https://prove2.me/theorems/12d5e42e-f5f9-4f9f-88fe-0745e224f539
-- title:
--   Tuned Candidate: side Margin eq value
-- statement:
--   The Tuned Candidate construction uses the side Margin eq value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedCandidate.lean#L215-L220
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedCandidate.lean#L215-L220

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem RH.Transport.TunedCandidate.sideMargin_eq_value (term : SideCondition) :
    sideMargin term = sideMarginValue term := by sorry
