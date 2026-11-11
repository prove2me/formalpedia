-- Prove2me | Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat33_epsilon_three_sandwich
-- name    : ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_epsilon_three_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T07:51:02.566934+00:00
-- url     : https://prove2.me/theorems/ac43f59a-1f09-4b97-81e4-58d0866b5beb
-- title:
--   Epsilon over three sandwich for smooth-cutoff approximations
-- statement:
--   When smooth-cutoff approximations converge first as time tends to zero and then as cutoff scale tends to infinity, with discrepancy controlled by vanishing annulus integrals, the sharp target sequence converges.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L3544-L3662

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_epsilon_three_sandwich {M : ℝ} (hM : 0 ≤ M)
    {A B : ℕ → ℝ} {a b : ℕ → ℕ → ℝ} {c : ℕ → ℝ} {L : ℝ}
    (hA : Tendsto A atTop (𝓝 L))
    (hB : Tendsto B atTop (𝓝 0))
    (ha : ∀ n, Tendsto (a n) atTop (𝓝 (A n)))
    (hb : ∀ n, Tendsto (b n) atTop (𝓝 (B n)))
    (herr : ∀ n k, |c k - a n k| ≤ M * b n k) :
    Tendsto c atTop (𝓝 L) := by sorry
