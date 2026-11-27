-- Prove2me | Theorems.Thm_SpilloverDuopoly_Switchers_Supplement_theorem_D1
-- name    : SpilloverDuopoly.Switchers.Supplement.theorem_D1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T22:41:11.706072+00:00
-- url     : https://prove2.me/theorems/fed72ab3-dabb-49e6-824b-02d266f6222c
-- title:
--   Theorem D.1, p. 51 (PDF 53) — with N > 2 firms and two periods, every symmetric equilibrium has p∗ = c − δπ^{R∗} and zero profit
-- statement:
--   Consider the two-period game with $N>2$ firms, common marginal cost $c\ge 0$ and discount factor $\delta\in[0,1]$. Fix any second-period equilibrium in which every firm earns the same profit $\pi^{R*}$ per unit of its own first-period share from its repeat consumers, any admissible first-period shares $\lambda_1,\dots,\lambda_N\ge 0$ with $\sum_j\lambda_j=1$, and a common first-period price $p$ at which consumers buy ($u_0\le V-p$). Then
--
--   $$
--   \text{all firms charging } p \text{ is a symmetric equilibrium}\iff p=p^*=c-\delta\pi^{R*},
--   $$
--
--   and in such an equilibrium every firm's profit in the two-stage pricing game is $0$.
--
--   Compared with Theorem 1 for two firms, where each firm earns $\delta\pi^{S*}$, a third firm drives the switching profit to zero: every switcher can choose among at least two untried products, so overall profit vanishes.
--
--   **Formalization Note** $\rho$ does not appear: it enters only through the demand of the second-period segments, over which the statement quantifies.
--
--   Differences from the source:
--   - generalization: consumers with jointly normal valuations (common correlation ρ) choosing by expected utility → any segment demand system in which the products a segment has not tried are perfect substitutes (UntriedSubstitutes: nonnegative demand, no demand without an offer, only the cheapest untried product sells, an untried firm that undercuts all other untried prices captures at least the whole untried demand); reason: The two-period source terminal demand has the four substitution properties on PDF 52. All valid source valuation/correlation instances are included; no Gaussian cutoff division or nonsingularity assumption is added.
--   - reading: π^{R∗}: firm i's second-period profit from repeat consumers is λ_iπ^{R∗} in a symmetric equilibrium → any second-period equilibrium (o2) with piK o2 k k = π^{R∗} for every firm k; reason: symmetry of the equilibrium makes the repeat profit per unit of share common to all firms, as the notation on p. 51 presumes
--   - reading: any symmetric equilibrium with any market share λ_i ∈ [0,1] (shares summing to one) → hypothesis u0 ≤ V − p: consumers buy at the common price; reason: shares summing to one presuppose that the market is covered at p, as in the published base Theorem 1; without it nobody buys and the price is undetermined
--   - generalization: the first-period price in any symmetric equilibrium is p∗ and profit is zero → a covered common price is a symmetric equilibrium iff it equals p∗, and then all profits are zero; reason: the forward direction is the source claim; the converse (p∗ is an equilibrium) is added, as in the base Theorem 1
--   - encoding: any market share λ_i ∈ [0,1] → any admissible tie rule, λ_i = tie(univ, i), shares nonnegative and summing to one; reason: same set of share vectors; the rule also fixes shares after deviations
--   - encoding: a firm may 'not sell' to a segment in a later period → later-period offers are Option ℝ (none = no sale, with zero demand); first-period prices are real numbers; reason: a first-period price above the rivals' already gives zero sales, as in the base mission
--   - generalization: one switching price S_i per firm, common to all its switchers (PDF 52, "S_i = c for all i") → each firm makes a separate offer to every first-period segment k, so switching prices may differ by origin segment; reason: segment payoffs are additive and the source's second-period equilibrium (S_i = c, repeat prices R_i) is a Nash equilibrium of every segment game, so every source second-period equilibrium satisfies IsSecondEq
-- source:
--   Chen, Stanton & Thomas, Information spillovers in experience goods competition, accepted manuscript (Management Science 70(6), 2024; LSE Research Online eprint 120790, version of June 18, 2023), p. 51 (PDF 53), Theorem D.1

import Mathlib
import Definitions.Def_SpilloverDuopoly_Switchers_Supplement_TwoPeriodNFirm

namespace SpilloverDuopoly.Switchers.Supplement

/-- Theorem D.1 (p. 51 (PDF 53)): with `N > 2` firms and two periods, for any second-period
equilibrium in which every firm earns the same repeat profit `π^{R∗}` per unit of its own
first-period share, and any admissible tie shares, a common first-period price `p` at which
consumers buy is a symmetric equilibrium iff `p = c - δ π^{R∗}`, and then every firm's profit in
the two-stage game is zero. -/
theorem theorem_D1 {N : ℕ} (hN : 2 < N) (G : TwoPeriodNFirm N) (hG : G.Standing)
    (o2 : Fin N → Fin N → Offer) (ho2 : G.IsSecondEq o2) (piR : ℝ)
    (hR : ∀ k, G.piK o2 k k = piR) (p : ℝ) (hcov : G.u0 ≤ G.V - p) :
    (G.IsSymEq o2 p ↔ p = G.c - G.delta * piR) ∧
    (G.IsSymEq o2 p → ∀ i, G.profit o2 (fun _ => p) i = 0) := by sorry

end SpilloverDuopoly.Switchers.Supplement
