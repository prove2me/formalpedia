-- Prove2me | Theorems.Thm_RH_Transport_TunedCandidate_intermediate_exceeds_cushion
-- name    : RH.Transport.TunedCandidate.intermediate_exceeds_cushion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:27:00.724886+00:00
-- url     : https://prove2.me/theorems/4ef71fff-20f6-49b1-996d-55cc540055d2
-- title:
--   Tuned Candidate: intermediate exceeds cushion
-- statement:
--   The Tuned Candidate construction uses the intermediate exceeds cushion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedCandidate.lean#L230-L232
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedCandidate.lean#L230-L232

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem RH.Transport.TunedCandidate.intermediate_exceeds_cushion : cushion < sideMargin .intermediate := by sorry
