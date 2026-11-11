-- Prove2me | Theorems.Thm_PriceCapacities_LowerBound_section_10_7_cost_eq_min_capacitated
-- name    : PriceCapacities.LowerBound.section_10_7_cost_eq_min_capacitated
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:24:17.621575+00:00
-- url     : https://prove2.me/theorems/2d93ea02-8eb7-434a-b013-5dc027e30089
-- title:
--   §10.7 display — $\mathrm{cost}_S(C)=\min_{h\in H}\mathrm{cost}_S(C,h)$, so a capacitated coreset preserves the unconstrained cost
-- statement:
--   Let $z\ge1$ and $k\ge1$ be integers. For every finite weighted point set $S$ in $\mathbb R^d$ and every center tuple $C\in(\mathbb R^d)^k$,
--   $$\mathrm{cost}_S(C)=\min_{h\in H}\mathrm{cost}_S(C,h),$$
--   where $\mathrm{cost}_S(C)=\sum_{x\in S}S(x)\min_i\|x-c_i\|^z$ is the unconstrained cost and the minimum ranges over nonnegative loads summing to the total mass $\mathbf 1(S)$ (the minimum is attained). Consequently, for $0<\varepsilon<1$, if $Q$ is a capacitated $\varepsilon$-coreset for $P$ then
--   $$|\mathrm{cost}_Q(C)-\mathrm{cost}_P(C)|\le\varepsilon\,\mathrm{cost}_P(C)\qquad\text{for every }C,$$
--   i.e. a coreset preserving every prescribed-load cost also preserves the ordinary clustering cost. This lets unconstrained lower bounds transfer to capacitated coresets.
--
--   Differences from the source:
--
--   - generalization: the display in §10.7, where k ∈ {2, 3} and ε < 1/4 → every k ≥ 1 and, in the second clause, every 0 < ε < 1; reason: the display is stated for every fixed center tuple without using k ≤ 3; Definition 2.2 takes ε ∈ (0, 1); the §10.7 case is a special case
--   - encoding: min_{h∈H} → ∃ h ∈ H attaining the value, and the value is ≤ cost_S(C, h) for every h ∈ H; reason: a minimum is an attained lower bound
--   - reading: 'a coreset preserving every prescribed-load cost also preserves the ordinary clustering cost' → |cost_Q(C) − cost_P(C)| ≤ ε cost_P(C) for every C whenever Q is a capacitated ε-coreset for P; reason: the ε-coreset guarantee for the unconstrained cost
--   - encoding: center tuples C ∈ (ℝ^d)^k, loads h ∈ ℝ^k_{≥0} with Σh_i = n, indices 1..k → C : Fin k → ℝ^d (repetitions allowed), h : Fin k → ℝ with h ≥ 0 and Σh = 1(P), 0-based; reason: same objects; Lean index base
-- source:
--   Prabhu, Schwiegelshohn, Shyam, The Price of Capacities for Clustering Coresets, STOC 2027 submission (manuscript sha256 ec35f5ef…), p. 40, §10.7 (display cost_S(C) = min_{h∈H} cost_S(C, h))

import Mathlib
import Definitions.Def_PriceCapacities_LowerBound_WeightedSets
import Definitions.Def_PriceCapacities_LowerBound_CapacitatedCost
import Definitions.Def_PriceCapacities_LowerBound_CapacitatedCoreset
import Definitions.Def_PriceCapacities_LowerBound_DualCost

namespace PriceCapacities.LowerBound

theorem section_10_7_cost_eq_min_capacitated (d k z : ℕ) (hk : 1 ≤ k) (hz : 1 ≤ z) :
    (∀ (S : WeightedSet (EuclideanSpace ℝ (Fin d))) (C : Fin k → EuclideanSpace ℝ (Fin d)),
      (∃ h : Fin k → ℝ, IsFeasibleLoad (totalWeight S) h ∧
          unconstrainedCost (z : ℝ) S C = capCost (z : ℝ) S C h) ∧
        ∀ h : Fin k → ℝ, IsFeasibleLoad (totalWeight S) h →
          unconstrainedCost (z : ℝ) S C ≤ capCost (z : ℝ) S C h) ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ P Q : WeightedSet (EuclideanSpace ℝ (Fin d)), IsCapacitatedCoreset k (z : ℝ) ε P Q →
        ∀ C : Fin k → EuclideanSpace ℝ (Fin d),
          |unconstrainedCost (z : ℝ) Q C - unconstrainedCost (z : ℝ) P C|
            ≤ ε * unconstrainedCost (z : ℝ) P C := by sorry

end PriceCapacities.LowerBound
