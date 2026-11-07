-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat15_untilt_sinc_density_zero_atom
-- name    : ProbabilityTheory.leanlevy_chat15_untilt_sinc_density_zero_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T07:38:08.606202+00:00
-- url     : https://prove2.me/theorems/322377e7-cc55-411f-b553-133739f0750d
-- title:
--   Recover the original Lévy measure by inverting its sinc tilt
-- statement:
--   The density 1 minus sinc is positive away from zero, so a base measure with no origin atom can be uniquely reconstructed by inverse-density weighting.
-- source:
--   slink/LeanLevy 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineProof.lean lines 1491-1502 and LeanLevy/Levy/LevyKhintchineUniqueness.lean lines 447-458.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Real

theorem ProbabilityTheory.leanlevy_chat15_untilt_sinc_density_zero_atom {ν : MeasureTheory.Measure ℝ} (hν0 : ν {(0 : ℝ)} = 0) : (ν.withDensity (fun x => ENNReal.ofReal (1 - Real.sinc x))).withDensity (fun x => (ENNReal.ofReal (1 - Real.sinc x))⁻¹) = ν := by sorry
