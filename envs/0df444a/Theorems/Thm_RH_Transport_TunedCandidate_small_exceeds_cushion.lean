-- Prove2me | Theorems.Thm_RH_Transport_TunedCandidate_small_exceeds_cushion
-- name    : RH.Transport.TunedCandidate.small_exceeds_cushion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:58:12.853974+00:00
-- url     : https://prove2.me/theorems/d179bb20-7c4f-424a-99b9-4316bfab9854
-- title:
--   Tuned Candidate: small exceeds cushion
-- statement:
--   The Tuned Candidate construction uses the small exceeds cushion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedCandidate.lean#L242-L244
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedCandidate.lean#L242-L244

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem RH.Transport.TunedCandidate.small_exceeds_cushion : cushion < sideMargin .small := by sorry
