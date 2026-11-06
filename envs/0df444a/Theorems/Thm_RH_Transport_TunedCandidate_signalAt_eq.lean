-- Prove2me | Theorems.Thm_RH_Transport_TunedCandidate_signalAt_eq
-- name    : RH.Transport.TunedCandidate.signalAt_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:26:32.76194+00:00
-- url     : https://prove2.me/theorems/d7afead5-0029-4b53-a028-12f6c7c1108a
-- title:
--   Tuned Candidate: signal At eq
-- statement:
--   The Tuned Candidate construction uses the signal At eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedCandidate.lean#L45-L47
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedCandidate.lean#L45-L47

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem RH.Transport.TunedCandidate.signalAt_eq (e b s : ℝ) : signalAt e b s = s - 2 / 3 - b / 6 := by sorry
