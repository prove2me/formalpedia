-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat15_lintegral_sinc_from_min_bound
-- name    : ProbabilityTheory.leanlevy_chat15_lintegral_sinc_from_min_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:27:55.249355+00:00
-- url     : https://prove2.me/theorems/86591f7e-56a2-4e19-8aed-0ac2626cd38a
-- title:
--   Finite sinc damping mass from finite minimum-square envelope
-- statement:
--   The ENNReal lintegral of one minus sinc is finite for any measure with integrable min-one-square and the pointwise sinc estimate.
-- source:
--   slink/LeanLevy 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineUniqueness.lean lines 87–99, source-exact conditional reduction with assumptions made explicit.

import Mathlib
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat15_lintegral_sinc_from_min_bound {ν : MeasureTheory.Measure ℝ}
    (hfinite : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ⊤)
    (hbound : ∀ x : ℝ, 1 - Real.sinc x ≤ 2 * min 1 (x ^ 2)) :
    ∫⁻ x, ENNReal.ofReal (1 - Real.sinc x) ∂ν < ⊤ := by sorry
