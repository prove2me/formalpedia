-- Prove2me | Theorems.Thm_PPDifferentiation_ShortRun_proposition_5
-- name    : PPDifferentiation.ShortRun.proposition_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T12:59:09.11599+00:00
-- url     : https://prove2.me/theorems/1922c471-4539-4b43-9173-c63bd065db03
-- title:
--   Proposition 5 — neither firm implements PP when decisions precede positioning
-- statement:
--   Let consumers be uniform on $[0,1]$, let $t>0$ be the quadratic misfit parameter, and let $F\ge0$ be the fixed PP implementation cost. Firms first choose PP or uniform pricing, then choose any real positions, then compete in prices. The uniform-price firm moves first when exactly one firm uses PP. The source's uniform, both-PP and two reflected asymmetric positioning outcomes are equilibria, and optimal uniform-leader prices exist in both asymmetric outcomes.
--
--   For every such pair of optimal leader prices, uniform pricing is strictly dominant for each firm. Consequently, the unique pure Nash equilibrium of the implementation game is
--
--   $$s_A=s_B=U.$$
--
--   Thus neither firm implements personalized pricing at any nonnegative implementation cost, including $F=0$.
--
--   **Formalization Note** Stage-1 payoffs are computed from consumer-level pricing profits, not entered as the numbers in Table 1. Position deviations range over all real locations. At off-path coincident locations the asymmetric position predicate selects an optimal pricing continuation; the paper does not specify off-path tie selection. The mirrored B-implements-PP positioning case follows the paper's symmetry convention. Reservation value is omitted under full market coverage; uniform-price ties are split equally.
-- source:
--   Li, Wang, Nault, Is Personalized Pricing Profitable When Firms Can Differentiate?, working paper, SSRN abstract 3881900 (version of August 3, 2021), §6, p. 25, Proposition 5; §6, pp. 23–25, subgames and Table 1

import Mathlib
import Definitions.Def_PPDifferentiation_ShortRun_Setting

namespace PPDifferentiation.ShortRun

theorem proposition_5 (t F : ℝ) (ht : 0 < t) (hF : 0 ≤ F) :
    IsPosEqUU t (-1/4) (5/4) (3*t/2) (3*t/2) ∧
    PPDifferentiation.Costless.IsPosEqPP t (1/4) (3/4) ∧
    IsPosEqAS t (-1/2) (1/2) ∧
    IsPosEqAS t (3/2) (1/2) ∧
    (∃ p₀ p₁ : ℝ, PPDifferentiation.Costless.IsLeaderOpt t (1/2) (-1/2) p₀ ∧
      PPDifferentiation.Costless.IsLeaderOpt t (1/2) (3/2) p₁) ∧
    ∀ p₀ p₁ : ℝ, PPDifferentiation.Costless.IsLeaderOpt t (1/2) (-1/2) p₀ →
      PPDifferentiation.Costless.IsLeaderOpt t (1/2) (3/2) p₁ →
      (∀ sB : PPChoice, stage1A t F p₀ p₁ .PP sB < stage1A t F p₀ p₁ .U sB) ∧
      (∀ sA : PPChoice, stage1B t F p₀ p₁ sA .PP < stage1B t F p₀ p₁ sA .U) ∧
      (∀ sA sB : PPChoice, IsPureNE (stage1A t F p₀ p₁) (stage1B t F p₀ p₁) sA sB ↔
        sA = .U ∧ sB = .U) := by sorry

end PPDifferentiation.ShortRun
