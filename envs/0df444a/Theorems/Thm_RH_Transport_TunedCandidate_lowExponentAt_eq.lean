-- Prove2me | Theorems.Thm_RH_Transport_TunedCandidate_lowExponentAt_eq
-- name    : RH.Transport.TunedCandidate.lowExponentAt_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:26:47.04391+00:00
-- url     : https://prove2.me/theorems/577eb937-93dc-44b9-b68e-1dd7e8e919c3
-- title:
--   Tuned Candidate: low Exponent At eq
-- statement:
--   The Tuned Candidate construction uses the low Exponent At eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedCandidate.lean#L49-L52
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedCandidate.lean#L49-L52

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem RH.Transport.TunedCandidate.lowExponentAt_eq (e b : ℝ) :
    lowExponentAt e b = 1 / 4 - e / 4 - b / 6 := by sorry
