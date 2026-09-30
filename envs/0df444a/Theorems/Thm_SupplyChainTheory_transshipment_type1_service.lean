-- Prove2me | Theorems.Thm_SupplyChainTheory_transshipment_type1_service
-- name    : SupplyChainTheory.transshipment_type1_service
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:09:57.960956+00:00
-- url     : https://prove2.me/theorems/2b4fbeff-8127-4a0d-aaa9-45481e2e3087
-- title:
--   Theorem 7.2: transshipments raise the type-1 service level by $|\partial \mathbb{E}[Y_{ji}]/\partial S_i|$
-- statement:
--   **Theorem 7.2.** Two retailers with base-stock levels $S_i, S_j$ face independent demands
--   $D_i, D_j$ with continuous distributions and finite means, and transship under complete
--   pooling: after demand is observed, $Y_{ji} = \min\{S_j - D_j, D_i - S_i\}$ units move from $j$
--   to $i$ when $j$ has a surplus and $i$ a shortage. Then transshipments increase the type-1
--   service level at $i$ by the marginal decrease in the expected transshipment quantity for a
--   unit increase in the base-stock level:
--
--   $$ \alpha_i(S) \;=\; \alpha^0_i(S) + \left|\frac{\partial\,\mathbb{E}[Y_{ji}]}{\partial S_i}\right|, $$
--
--   where $\alpha^0_i(S) = \Pr[D_i \le S_i]$ is the service level without transshipments and
--   $\alpha_i(S)$ is the probability that the shortage at $i$ is covered. The derivative exists
--   and is nonpositive (Eq. 7.15): raising $S_i$ reduces what $i$ needs from $j$, and by exactly
--   the probability that a transshipment covers the shortage.
--
--   **Formalization Note** The book differentiates the density formula (7.8) by Leibniz's rule;
--   the statement here assumes only that the two laws have no atoms and finite means, which is
--   what makes $\mathbb{E}[Y_{ji}]$ differentiable in $S_i$ with the stated derivative.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 242, Sect. 7.4.4, Theorem 7.2 and its proof, Eq. (7.12)-(7.16); the model is Sect. 7.4.2 pp. 237-239; after Tagaras (1989)

import Definitions.Def_SupplyChainTheory_flexibility

namespace SupplyChainTheory

theorem transshipment_type1_service (Sj Si : ℝ) (Dj Di : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure Dj] [MeasureTheory.IsProbabilityMeasure Di]
    [MeasureTheory.NullSingletonClass Dj] [MeasureTheory.NullSingletonClass Di]
    (hj : MeasureTheory.Integrable (fun x => x) Dj)
    (hi : MeasureTheory.Integrable (fun x => x) Di) :
    ∃ dY : ℝ, HasDerivAt (fun s => expTransship Sj s Dj Di) dY Si ∧ dY ≤ 0
      ∧ type1Trans Sj Si Dj Di = type1NoTrans Si Di + |dY| := by sorry

end SupplyChainTheory
