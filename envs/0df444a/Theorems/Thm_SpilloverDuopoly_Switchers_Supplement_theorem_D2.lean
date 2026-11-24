-- Prove2me | Theorems.Thm_SpilloverDuopoly_Switchers_Supplement_theorem_D2
-- name    : SpilloverDuopoly.Switchers.Supplement.theorem_D2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T22:42:03.312092+00:00
-- url     : https://prove2.me/theorems/bdb21332-089a-4798-91cc-1dac7a2e683a
-- title:
--   Theorem D.2, p. 54 (PDF 56) — T = 3, N = 4: a symmetric equilibrium at p∗ = c − δΠ₁ with Π₁ ≥ 0 and zero overall profit
-- statement:
--   Consider four firms and three periods with common marginal cost $c\ge0$, discount factor $\delta\in[0,1]$, and persistent jointly normal consumer values having common mean $\mu\in\mathbb R$, standard deviation $\sigma>0$ and correlation $\rho\in[0,1]$. Consumers learn only tried values and maximize discounted expected utility, including future experimentation. Fix a symmetric continuation equilibrium: terminal offers respond to every second-period offer profile, consumers optimize against these responses, and firms optimize their actual selected-history profits. First-period tie shares are any admissible nonnegative shares, including zeros.
--
--   For firm 1 define the period-2-valued continuation profit from its own first-period consumers by
--   $$\Pi_1=\pi_1^1+\delta\sum_{l=0}^4\pi_1^{1l}.$$
--   Suppose consumers buy at the candidate price, $u_0\le V-(c-\delta\Pi_1)$, where $V$ is the computed gross value of a first-period trial. There exists a symmetric first-period equilibrium price $p$ such that
--   $$p=p^*=c-\delta\Pi_1,\qquad\Pi_1\ge0,\qquad \text{overall profit}_i=0\quad(i=1,2,3,4).$$
--   Overall profit is the original sum of first-period margins and all initial-share-weighted continuation profits, with discount powers $\delta$ and $\delta^2$. It has not been defined using cancellation. This is the three-period companion to the published two-period goal.
--
--   **Formalization Note** Firm 1 is index 0. Conditional expectations handle the correlation endpoints without division by zero. The theorem is an open statement; its proof, including switching-profit cancellation, remains the solvers' task.
--
--   Differences from the source:
--   - reading: There exists a symmetric equilibrium, immediately preceded by "in the first period" (PDF 56). → Every given symmetric source continuation equilibrium extends to a symmetric first-period equilibrium at the stated price.; reason: The authorized first-period reading takes continuation equilibria as given rather than adding an unconditional existence claim for all continuation subgames.
--   - reading: Symmetric products and equilibrium. → Gaussian law invariant under firm relabelling, with price and consumer-strategy symmetry at all preceding offers, including deviations.; reason: On-path payoff symmetry alone does not specify the source symmetric continuation game; strategy symmetry expresses identical products and responses.
--   - reading: Covered first period, sum of initial shares equals one before (30) (PDF 55). → Explicit hypothesis u0 ≤ V − (c − δΠ_1).; reason: The brief and the base goal use this covered-market convention; all real-price deviations and no-sale choices remain available.
--   - encoding: Consumer learning and future option values (§2, D.4). → Conditional expectations on observed coordinates and optimal measurable choice probabilities; Gaussian law from independent common and individual shocks.; reason: Realize the normal source game and selected histories, retain rho=0 and rho=1, and avoid fixed-composition demand arrays.
--   - encoding: Equation (30) after Lemma D.2 removes untried histories. → Original total profit with full sums over all k and all l including outside.; reason: Untried-history contributions must be proved zero; no (31) identity or switching cancellation is assumed.
--   - reading: Firms price to purchase-history segments (proof of Lemma D.3, PDF 54: "S1, S3, S4 are firm 1, 3, 4's prices to customers who switch from product 2"; π_i^{kl} per segment). → Every firm makes a separate offer to every public history segment k (period 2) and (k, l) (period 3).; reason: Appendix D's proofs price each history segment separately, beyond §2's two-firm remark that switchers and non-buyers share a price; coverage leaves no first-period non-buyer segment.
-- source:
--   Chen, Stanton & Thomas, Information spillovers in experience goods competition, accepted manuscript (Management Science 70(6), 2024; LSE Research Online eprint 120790, version of June 18, 2023), p. 54 (PDF 56), Theorem D.2

import Mathlib
import Definitions.Def_SpilloverDuopoly_Switchers_Supplement_SourceThreePeriod

namespace SpilloverDuopoly.Switchers.Supplement

/-- Theorem D.2, accepted manuscript p.54 (PDF 56), in its governing sentence's
first-period sense: a given symmetric continuation equilibrium of the consumer-learning
game extends to a symmetric covered first-period equilibrium. The continuation subgames
are not assumed to exist unconditionally. All preceding-price-dependent selected laws,
consumer experimentation and off-path price responses are part of the game; neither
(31), switching-profit cancellation nor nonnegativity of Pi is a premise.

`0 : Fin 4` is the paper's firm 1. Coverage is disclosed separately, as for the base goal.
The existence, exact price, nonnegative continuation value and every firm's zero overall
profit are kept together. -/
theorem theorem_D2 (M : SourceMarket) (hM : M.Standing) (C : Consumers)
    (o2 : Fin 4 → Offers4) (o3 : SourceMarket.TerminalOffers)
    (hC : C.Rational M o3) (hsym : C.Symmetric o2 o3)
    (heq : (C.game M o2 o3).IsContEq o2 o3)
    (hcov : M.u0 ≤ C.gross1 M o2 o3 0 -
      (M.c - M.delta * (C.game M o2 o3).Pi o2 o3 0)) :
    ∃ p : ℝ, p = M.c - M.delta * (C.game M o2 o3).Pi o2 o3 0 ∧
      (C.game M o2 o3).IsSymFirstEq o2 o3 p ∧
      0 ≤ (C.game M o2 o3).Pi o2 o3 0 ∧
      ∀ i, (C.game M o2 o3).profit o2 o3 (fun _ => p) i = 0 := by sorry

end SpilloverDuopoly.Switchers.Supplement
