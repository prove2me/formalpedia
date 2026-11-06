-- Prove2me | Theorems.Thm_RH_Transport_TunedCandidate_intermediateExponent_eq
-- name    : RH.Transport.TunedCandidate.intermediateExponent_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:26:52.683932+00:00
-- url     : https://prove2.me/theorems/18a8f107-56b3-4476-b6a1-fd2a541a30e0
-- title:
--   Tuned Candidate: intermediate Exponent eq
-- statement:
--   The Tuned Candidate construction uses the intermediate Exponent eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedCandidate.lean#L151-L158
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedCandidate.lean#L151-L158

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem RH.Transport.TunedCandidate.intermediateExponent_eq (δ x : ℝ) :
    intermediateExponent δ x =
      -41270920211 / 187500000000 +
        (2662873553 / 15000000000) * δ +
        (625643953 / 3750000000) * δ * x := by sorry
