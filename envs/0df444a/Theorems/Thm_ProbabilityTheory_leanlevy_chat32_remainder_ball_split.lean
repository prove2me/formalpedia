-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat32_remainder_ball_split
-- name    : ProbabilityTheory.leanlevy_chat32_remainder_ball_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T23:44:55.555876+00:00
-- url     : https://prove2.me/theorems/38df35a9-31ec-40d5-bdf9-81b2dcae9325
-- title:
--   Split cubic remainder integral into inner ball and annular band
-- statement:
--   For positive inner and outer radii, the cubic remainder integral over the outer ball equals the integrals over the disjoint inner ball and intervening band.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L4344-L4387

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat32_remainder_ball_split {δ r : ℝ} (_hδ : 0 < δ) (hδr : δ < r) (_hr1 : r ≤ 1) (ξ : ℝ)
    (m : Measure ℝ)
    (hRint : IntegrableOn
      (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2)
      {x : ℝ | |x| < r} m) :
    ∫ x in {x | |x| < r},
        (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂m =
      (∫ x in {x | |x| < δ},
          (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂m) +
      ∫ x in {x | δ ≤ |x| ∧ |x| < r},
          (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂m := by sorry
