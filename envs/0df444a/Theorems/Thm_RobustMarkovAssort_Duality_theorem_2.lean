-- Prove2me | Theorems.Thm_RobustMarkovAssort_Duality_theorem_2
-- name    : RobustMarkovAssort.Duality.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:17:09.895634+00:00
-- url     : https://prove2.me/theorems/92b150be-26a1-46ac-86df-c727cec8fcec
-- title:
--   Theorem 2 — general min–max duality and optimal tight assortment
-- statement:
--   Under Assumptions 3–6, the general mapping (4) is defined on every real vector and has a unique fixed point v*. There is a common attained value z of max_S min_u RGen(S,u) and min_u max_S RGen(S,u), with all inner extrema attained. The full equality set S*={i : v*_i=r_i} has worst-case revenue z and is therefore an optimal robust assortment. No uniqueness of the assortment is asserted.
--
--   Differences from the source:
--   - encoding: products numbered 1 through n and arbitrary subsets of N → products Fin n and assortments Finset (Fin n); reason: the index shift is a bijection and every subset is represented
--   - generalization: a finite universe of products → n may also be zero; reason: the empty universe has one empty vector and one assortment, all revenues are zero, and every claimed extremum and fixed point exists uniquely there
--   - reading: uncertainty sets of possible model parameters → each parameter set is explicitly nonempty; reason: a possible-parameter set is read as containing at least one scenario, consistent with the choice of u0 on page 19
--   - reading: equivalent optimization programs with nested minima in Assumptions 5 and 6 → equal attained least objective values with inner weight minima defined on the relational feasible domain; reason: this makes optimal-value equivalence explicit without requiring pointwise simultaneous optimizers; missing row minima do not receive defaults
--   - encoding: the unique balance solution defines revenue → inverse of the matrix with identity rows on offered products and A rows elsewhere; reason: Assumption 4, or the Markov specialization under Assumption 2, makes this matrix strictly diagonally dominant and invertible
--   - encoding: the displayed min and max values → IsLeast and IsGreatest objective-image relations, including every inner extremum; reason: membership expresses attainment and the order bound expresses optimality
--   - encoding: the displayed mapping is defined on all real vectors and has a unique fixed point → existence of its row-minimum map on every real vector and a unique fixed point of the componentwise maximum; reason: the map is pinned to the actual attained minima in the conclusion rather than assuming their existence
-- source:
--   Désir, Goyal, Jiang, Xie and Zhang, Robust Assortment Optimization Under the Markov Chain Choice Model, Operations Research (2023), DOI 10.1287/opre.2022.2420; canonical artifact PDF/printed p. 12, Theorem 2

import Definitions.Def_RobustMarkovAssort_Duality_GeneralPrograms

namespace RobustMarkovAssort.Duality

theorem theorem_2 {n : ℕ} {α : Type*} (G : GeneralModel n α)
    (h3 : Assumption3 G) (h4 : Assumption4 G)
    (h5 : Assumption5 G) (h6 : Assumption6 G) :
    ∃ m : Vec n → Vec n, (∀ v i, RowMin G v i (m v i)) ∧
      ∃ v : Vec n, fixedMap G.r m v = v ∧
        (∀ w, fixedMap G.r m w = w → w = v) ∧
        ∃ z : ℝ, MaxMin G.U (revenue G) z ∧ MinMax G.U (revenue G) z ∧
          MinValue G.U (revenue G (tightSet G.r v)) z := by sorry

end RobustMarkovAssort.Duality
