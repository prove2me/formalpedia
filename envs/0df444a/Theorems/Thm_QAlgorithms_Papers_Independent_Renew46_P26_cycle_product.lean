-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P26_cycle_product
-- name    : QAlgorithms.Papers.Independent.Renew46.P26.cycle_product
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:04:55.925977+00:00
-- url     : https://prove2.me/theorems/1ac5b12b-42bf-48f0-86cf-c99b25b64c1a
-- title:
--   Unnumbered YJM cycle-product identity (8.2)
-- statement:
--   For every $k\geq1$, in the actual complex group algebra of $S_k$,
--
--   $$X_2X_3\cdots X_k=\sum_{g\text{ a full }k\text{-cycle}}g.$$
--
--   Every full cycle is included exactly once. At $k=1$ the product is empty and the unique one-letter cycle is the identity. This identity concerns cycles using all letters, rather than cycles of arbitrary smaller length.
-- source:
--   A New Approach to the Representation Thoery of the Symmetric Groups. 2, arXiv:math/0503040v3, PDF p. 28, Unnumbered YJM cycle-product identity (8.2)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Equation (8.2) (PDF p.28). Product X_2...X_k equals the sum of all full
k-cycles, each once. k≥1; for k=1 the empty product and the unique cycle are 1. -/
theorem cycle_product (k : ℕ) (hk : 1 ≤ k) :
    (List.ofFn (fun i : Fin (k - 1) => yjm (⟨i.val + 1, by omega⟩ : Fin k))).prod =
      ∑ g ∈ Finset.univ.filter (fun g : Equiv.Perm (Fin k) => IsFullCycle g),
        MonoidAlgebra.single g (1 : ℂ) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P26

end
