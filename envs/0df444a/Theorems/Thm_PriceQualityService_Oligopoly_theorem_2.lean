-- Prove2me | Theorems.Thm_PriceQualityService_Oligopoly_theorem_2
-- name    : PriceQualityService.Oligopoly.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:32.48322+00:00
-- url     : https://prove2.me/theorems/e0e8b877-c378-46b1-b716-ed98fe58f33f
-- title:
--   Theorem 2: the price–quality–service oligopoly has a unique Nash equilibrium, with monopoly qualities and durations and lower prices
-- statement:
--   Consider $N$ firms, firm $i$ selling product $i$ under MNL demand. Firm $i$ simultaneously chooses a price $p_i \in \mathbb R$, a quality level $q_i \in \mathbb R$ and a service duration $t_i \in [t_s, t_l]$, and its payoff is
--   $$
--   \Pi_i(\mathbf p, \mathbf q, \mathbf t; \mathcal N) = \big[p_i - c_i q_i^2 - t_i(a_i - b_i q_i)\big] \cdot \frac{\exp(\alpha_i q_i - p_i + t_i s_i)}{1 + \sum_{j \in \mathcal N} \exp(\alpha_j q_j - p_j + t_j s_j)} .
--   $$
--   Assume $c_i > 0$ for all $i$, $t_s < t_l$, and that no firm is indifferent between the two extreme durations:
--   $$
--   \varphi_i(t_s) \ne \varphi_i(t_l), \qquad \varphi_i(t) = \frac{b_i^2 t^2}{4 c_i} + \Big(s_i - a_i + \frac{\alpha_i b_i}{2 c_i}\Big) t .
--   $$
--   Then:
--
--   1. the game has exactly one pure-strategy Nash equilibrium $(\mathbf p^o, \mathbf q^o, \mathbf t^o)$;
--   2. the monopolist's problem (4), maximizing $\sum_i \Pi_i$ over $\mathbf p, \mathbf q \in \mathbb R^N$ and $\mathbf t \in [t_s, t_l]^N$, has an optimal solution;
--   3. for every optimal solution $(\mathbf p^*, \mathbf q^*, \mathbf t^*)$ of (4), $\mathbf t^o = \mathbf t^*$, $\mathbf q^o = \mathbf q^*$ and $p_i^o \le p_i^*$ for every $i$.
--
--   So competition does not change the quality and service decisions of the firms, only their prices, which fall.
--
--   **Formalization Note** The no-indifference hypothesis is added: if $\varphi_i(t_s) = \varphi_i(t_l)$ for some $i$, firm $i$ has two best responses that differ in $(p_i, q_i, t_i)$ and leave the other firms' payoffs unchanged, so the equilibrium is not unique; the paper's proof silently picks one endpoint. "Lower prices" is stated as $p_i^o \le p_i^*$, which is what the paper's proof derives (with $N = 1$ the two problems coincide). The existence of a monopoly optimum (Theorem 1) is included so that the comparison is not vacuous. $N$ is arbitrary.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), p. 14, Theorem 2 (with eq. (6)); proof in Online Supplement pp. 2–3 (PDF pp. 35–36)

import Mathlib
import Definitions.Def_PriceQualityService_Oligopoly_Model

namespace PriceQualityService.Oligopoly

/-- Theorem 2 (Wang, Ke & Cui, p. 14): under joint competition in price, quality level and
service duration there is a unique Nash equilibrium; its service durations and quality levels
are those of the monopolistic problem (4), and its prices are no higher than the monopoly
prices. Hypotheses: `c_i > 0`, `t_s < t_l`, and no firm is indifferent between the two extreme
durations (`durationIndex i t_s ≠ durationIndex i t_l`). A monopoly optimum exists, so the
comparison is not vacuous. -/
theorem theorem_2 {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (ts tl : ℝ)
    (hst : ts < tl)
    (hnt : ∀ i, durationIndex α a b c s i ts ≠ durationIndex α a b c s i tl) :
    (∃! x : Fin N → ℝ × ℝ × ℝ, IsOligopolyEquilibrium α a b c s ts tl x) ∧
      (∃ p q t : Fin N → ℝ, IsMonopolyOptimum α a b c s ts tl p q t) ∧
      ∀ x : Fin N → ℝ × ℝ × ℝ, IsOligopolyEquilibrium α a b c s ts tl x →
        ∀ p q t : Fin N → ℝ, IsMonopolyOptimum α a b c s ts tl p q t →
          durations x = t ∧ qualities x = q ∧ ∀ i, prices x i ≤ p i := by sorry

end PriceQualityService.Oligopoly
