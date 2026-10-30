-- Prove2me | Theorems.Thm_RobustMarkovAssort_Duality_theorem_1
-- name    : RobustMarkovAssort.Duality.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:18:28.755856+00:00
-- url     : https://prove2.me/theorems/7db47ca2-ba4a-4c69-9d60-4427e5bc2376
-- title:
--   Theorem 1 — Markov min–max duality and optimal robust assortment
-- statement:
--   Under Markov Assumptions 1 and 2, the row minima in (2) exist on all real vectors and f_i(v)=max(r_i,min_q sum_j q_j v_j) has a unique fixed point v*. There is a common attained value z of max_S min_(rho,lambda) RMC and min_(rho,lambda) max_S RMC, with all inner extrema attained. The full equality set {i : v*_i=r_i} attains robust value z. Infinite and nonclosed uncertainty sets, zero prices and ties are included; no compactness or attainment hypothesis is added.
--
--   Differences from the source:
--   - encoding: products numbered 1 through n and arbitrary subsets of N → products Fin n and assortments Finset (Fin n); reason: the index shift is a bijection and every subset is represented
--   - generalization: a finite universe of products → n may also be zero; reason: the empty universe has one empty vector and one assortment, all revenues are zero, and every claimed extremum and fixed point exists uniquely there
--   - reading: uncertainty sets of possible model parameters → each parameter set is explicitly nonempty; reason: a possible-parameter set is read as containing at least one scenario, consistent with the choice of u0 on page 19
--   - generalization: arrival probabilities in the model description and strictly positive vectors in Assumption 2 → arbitrary strictly positive arrival weights without normalization; reason: the explicit assumption is positivity and all normalized probability instances specialize directly
--   - encoding: Assumption 1 states Cartesian row uncertainty → the model constructs exactly that Cartesian product, independently of arrival uncertainty; reason: the construction ranges over all and only the source scenarios
--   - encoding: the unique balance solution defines revenue → inverse of the matrix with identity rows on offered products and A rows elsewhere; reason: Assumption 4, or the Markov specialization under Assumption 2, makes this matrix strictly diagonally dominant and invertible
--   - encoding: the displayed min and max values → IsLeast and IsGreatest objective-image relations, including every inner extremum; reason: membership expresses attainment and the order bound expresses optimality
--   - encoding: the displayed mapping is defined on all real vectors and has a unique fixed point → existence of its row-minimum map on every real vector and a unique fixed point of the componentwise maximum; reason: the map is pinned to the actual attained minima in the conclusion rather than assuming their existence
-- source:
--   Désir, Goyal, Jiang, Xie and Zhang, Robust Assortment Optimization Under the Markov Chain Choice Model, Operations Research (2023), DOI 10.1287/opre.2022.2420; canonical artifact PDF/printed p. 9, Theorem 1

import Definitions.Def_RobustMarkovAssort_Duality_MCPrograms

namespace RobustMarkovAssort.Duality

theorem theorem_1 {n : ℕ} (M : MCUncertainty n) (h2 : Assumption2 M) :
    ∃ m : Vec n → Vec n, (∀ v i, MCRowMin M v i (m v i)) ∧
      ∃ v : Vec n, fixedMap M.r m v = v ∧
        (∀ w, fixedMap M.r m w = w → w = v) ∧
        ∃ z : ℝ, MaxMin Set.univ (mcRevenue M h2) z ∧
          MinMax Set.univ (mcRevenue M h2) z ∧
          MinValue Set.univ (mcRevenue M h2 (tightSet M.r v)) z := by sorry

end RobustMarkovAssort.Duality
