-- Prove2me | Theorems.Thm_PLCMarkets_Rationality_lp_optimal_value_eq_total_money
-- name    : PLCMarkets.Rationality.lp_optimal_value_eq_total_money
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T01:00:22.830977+00:00
-- url     : https://prove2.me/theorems/9f19daec-18ff-4256-a876-0bca80f7e194
-- title:
--   Proof of THEOREM 4.1 — the starting equilibrium prices p′ are an optimal LP solution of value M
-- statement:
--   Let $M$ be a Fisher market with additively separable piecewise-linear concave utilities, and let $p'$ be equilibrium prices with $p'_j>0$ for every good and $\sum_jp'_j=\sum_ie(i)$. Consider the linear program of Section 4 built from $p'$ (see `RationalityLP`). Then there is a flow $f$ such that $(p',f)$ is an optimal solution of this LP, and its objective value is the total money:
--   $$f_{(t,s)}+\sum_{i\in B}\mathrm{spent}(i)=\sum_{i\in B}e(i).$$
--
--   Together with the statement that every optimal solution with positive prices is an equilibrium, this shows that the LP's optimal face contains $p'$ and consists of equilibria, so a rational optimal solution gives rational equilibrium prices.
--
--   **Formalization Note.** Positivity of $p'$ and $\sum_jp'_j=\sum_ie(i)$ are the standing assumptions of Section 3 under which the forced/flexible classes, and hence the LP, are defined; the LP's constraint $\sum_jp_j=M$ can be met by $p'$ only under the second.
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, https://doi.org/10.1145/1970392.1970394, p. 10:9, proof of THEOREM 4.1, first sentence

import Mathlib
import Definitions.Def_PLCMarkets_Rationality_RationalityLP

namespace PLCMarkets.Rationality

/-- **Proof of THEOREM 4.1, first sentence** (Vazirani–Yannakakis 2011, §4, p. 10:9): the
starting equilibrium prices `p'`, together with a flow, form an optimal solution of value `M`
(the total money of the buyers) of the LP constructed from `p'`. The prices `p'` are positive and sum
to the total money (the standing assumptions of Section 3 under which the LP's data are
defined). -/
theorem lp_optimal_value_eq_total_money {n g : ℕ} (M : FisherMarket n g) (p' : Fin g → ℝ)
    (hp' : M.IsEquilibrium p')
    (hpos : ∀ j, 0 < p' j)
    (hsum : ∑ j, p' j = ∑ i, (M.budget i : ℝ)) :
    ∃ z : FisherMarket.LPPoint n g, z.p = p' ∧ M.IsLPOptimal p' z ∧
      M.lpObjective p' z = ∑ i, (M.budget i : ℝ) := by sorry

end PLCMarkets.Rationality
