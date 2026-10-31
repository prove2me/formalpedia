-- Prove2me | Theorems.Thm_PlatformPreannouncement_SHNSW_proposition_1
-- name    : PlatformPreannouncement.SHNSW.proposition_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:18:58.72444+00:00
-- url     : https://prove2.me/theorems/aebd14e9-67cf-4d63-a575-5706b4db15df
-- title:
--   Proposition 1 — Formal preannouncement with strong taste preferences
-- statement:
--   Consider two identical platform firms at the endpoints of $[0,1]$, with separate uniform unit new markets of users and developers and loyal installed bases of mass $1/2$ per firm on each side. All agents single-home and old agents adopt the new version without switching. The real transport, same-side user externality, cross-side externality, intrinsic value and formal cost parameters satisfy $t,\alpha,\beta,\theta,c>0$. The informal cost multiplier and information parameters satisfy $0<k\le1$ and $0<\mu\le\delta<1$.
--
--   Firms simultaneously choose formal ($F$), informal ($I$), or no ($N$) announcement and then simultaneously choose a nonnegative user price and developer licensing fee. For these modes the user-information multiplier $a_i$, developer-information multiplier $b_i$, and cost $C_i$ are $(1,1,c)$, $(\mu,\delta,kc)$, and $(0,0,0)$. Given new market shares $n_u^i,n_d^i$, expected values before transport and net firm profit are
--   $$V_u^i=\theta+\alpha(1/2+a_i n_u^i)+\beta(1/2+a_i n_d^i)-p_i,
--   \quad V_d^i=\theta+\beta(1/2+b_i n_u^i)-l_i,$$
--   $$\Pi_i=p_i(1/2+n_u^i)+l_i(1/2+n_d^i)-C_i.$$
--   Location utility subtracts $tx$ or $t(1-x)$. Each new side is fully covered with shares in $[0,1]$. Its cutoff allocation maximizes utility and gives nonnegative utility to all served agents; the cutoffs also supply the demands in these same expected values. Boundary cutoffs use weak choice inequalities. Information multipliers do not change at the pricing stage.
--
--   Maintain the paper's explicit formal-candidate economic conditions:
--   $$t>\alpha,\quad t(t-\alpha)>\beta^2,\quad t>\alpha+\beta,\quad t>\beta,$$
--   $$4t\ge c+2\alpha+4\beta,\quad 5t\le2\theta+6\alpha+6\beta,\quad 5t\le2\theta+6\beta.$$
--   Suppose taste preferences lie in the exact open interval
--   $$\frac{2\theta+\beta(1+4\mu+\delta)}5<t<\frac{2\theta+6\beta}5.$$
--
--   Then there exists a fulfilled-expectation demand selection and a symmetric pure subgame-perfect equilibrium whose announcement pair is $(F,F)$, with both firms charging
--   $$p_i^*=2(t-\alpha-\beta),\qquad l_i^*=2(t-\beta).$$
--   Moreover, every symmetric pure subgame-perfect equilibrium, under any valid demand selection, has precisely this announcement pair and these on-path tariffs.
--
--   Here a strategy specifies continuation tariffs after all nine announcement pairs. Symmetry means equal initial announcements and equality of the firms' price plans upon interchanging their labels and the history. At every history, equilibrium tariffs have a feasible market and nonnegative profit; no firm gains from any unilateral jointly chosen price/fee pair admitting a feasible market with the opponent's tariffs fixed. At stage one, neither firm gains from changing its own announcement and using the corresponding continuation. A single demand selection supplies a feasible allocation at every history/tariff profile that admits one; no feasible tariff deviation can be discarded, and profit nonnegativity does not restrict deviations. A history without any feasible pricing equilibrium defeats existence rather than disappearing from the quantifier.
--
--   The source's proof gap in (A2) and the mislabeled formal-utility display are recorded separately as insights. Neither is assumed or used to replace the printed claim.
--
--   Differences from the source:
--   - reading: the paper computes interior covered demand and leaves boundary and off-path selection implicit → Lean uses the covered-market feasible-allocation relation, endpoint weak inequalities, and one selection valid wherever a feasible allocation exists, with every feasible unilateral tariff pair compared and all nine continuation histories required; reason: makes the maintained covered-market game operational without an uncovered-market extension or negative shares.
--   - reading: firms will pursue formal preannouncement in SPNE, within the symmetric pure equilibria studied on pp. 21–22 → Lean asserts existence with the printed outcome and characterizes every symmetric pure SPNE outcome; reason: retains the categorical claim and prevents a vacuous conditional-only statement.
--   - encoding: the paper uses named firms and uniform Hotelling locations → Lean uses two firm indices, ordered announcement pairs, real tariff pairs, and real cutoff lengths for each uniform unit continuum; reason: interval length equals market mass and an isolated tie has zero mass, so no market is discretized.
-- source:
--   Chellappa and Mukherjee (2020), Platform Preannouncement Strategies: The Strategic Role of Information in Two-Sided Markets Competition, DOI 10.1287/mnsc.2020.3606, published citation basis, held source.pdf Proposition 1 and interval p. 26, (A5) p. 47; standing assumptions pp. 10–25, economic inequalities pp. 46–47; proof pp. 45–48. PDF and printed pagination coincide. SHA256 9eca21f6eddbd20b896edc77778afd83d5648c3eb49ed19d2cb4747b4debea8c.

import Definitions.Def_PlatformPreannouncement_SHNSW_Equilibrium

namespace PlatformPreannouncement.SHNSW

theorem proposition_1
    (P : PlatformPreannouncement.SHNSW.Parameters)
    (ht : 0 < P.t) (halpha : 0 < P.alpha) (hbeta : 0 < P.beta)
    (htheta : 0 < P.theta) (hc : 0 < P.c)
    (hk : 0 < P.k ∧ P.k ≤ 1) (hinfo : 0 < P.mu ∧ P.mu ≤ P.delta ∧ P.delta < 1)
    (hconcave : P.alpha < P.t ∧ P.beta ^ 2 < P.t * (P.t - P.alpha))
    (htariffs : P.alpha + P.beta < P.t ∧ P.beta < P.t)
    (hprofit : P.c + 2 * P.alpha + 4 * P.beta ≤ 4 * P.t)
    (hparticipation : 5 * P.t ≤ 2 * P.theta + 6 * P.alpha + 6 * P.beta ∧
      5 * P.t ≤ 2 * P.theta + 6 * P.beta)
    (hstrong : (2 * P.theta + P.beta * (1 + 4 * P.mu + P.delta)) / 5 < P.t ∧
      P.t < (2 * P.theta + 6 * P.beta) / 5) :
    (∃ (D : PlatformPreannouncement.SHNSW.DemandSelection)
        (s : PlatformPreannouncement.SHNSW.StrategyProfile),
      PlatformPreannouncement.SHNSW.IsSPNE P D s ∧
      PlatformPreannouncement.SHNSW.Symmetric s ∧
      PlatformPreannouncement.SHNSW.FormalOutcome P s) ∧
    (∀ (D : PlatformPreannouncement.SHNSW.DemandSelection)
        (s : PlatformPreannouncement.SHNSW.StrategyProfile),
      PlatformPreannouncement.SHNSW.IsSPNE P D s →
      PlatformPreannouncement.SHNSW.Symmetric s →
      PlatformPreannouncement.SHNSW.FormalOutcome P s) := by sorry

end PlatformPreannouncement.SHNSW
