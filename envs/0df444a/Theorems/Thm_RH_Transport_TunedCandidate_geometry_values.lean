-- Prove2me | Theorems.Thm_RH_Transport_TunedCandidate_geometry_values
-- name    : RH.Transport.TunedCandidate.geometry_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:57:29.885208+00:00
-- url     : https://prove2.me/theorems/7bef282c-343b-4b69-8d70-0c997611573a
-- title:
--   Tuned Candidate: geometry values
-- statement:
--   The Tuned Candidate construction uses the geometry values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedCandidate.lean#L88-L93
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedCandidate.lean#L88-L93

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem RH.Transport.TunedCandidate.geometry_values :
    ell = 625643953 / 3750000000 ∧
    lx = 2661585647 / 7500000000 ∧
    ly = 3587126447 / 7500000000 ∧
    h = 2029900753 / 2500000000 := by sorry
