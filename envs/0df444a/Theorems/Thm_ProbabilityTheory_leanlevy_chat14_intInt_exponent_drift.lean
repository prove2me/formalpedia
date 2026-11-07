-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat14_intInt_exponent_drift
-- name    : ProbabilityTheory.leanlevy_chat14_intInt_exponent_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:10:15.666498+00:00
-- url     : https://prove2.me/theorems/a0604ffc-0b94-4e0c-adce-361bf2b3b8a6
-- title:
--   Drift cancellation in Levy exponent smearing
-- statement:
--   Symmetric integral of linear drift term in Lévy exponent equals twice its value at the centre.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineUniqueness.lean, original private intInt_exponent_drift; CHAT14 proof unchanged; prior auto-strict job f919c2c2 failed to parse.

import Mathlib
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat14_intInt_exponent_drift (b ξ : ℝ) :
    ∫ u in (-1 : ℝ)..1, ((b : ℂ) * ↑(ξ + u) * Complex.I)
      = 2 * (b : ℂ) * ↑ξ * Complex.I := by sorry
