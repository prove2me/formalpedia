-- Prove2me | Theorems.Thm_TestingEstimation_Dense_clipped_boosting
-- name    : TestingEstimation.Dense.clipped_boosting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:52.50296+00:00
-- url     : https://prove2.me/theorems/11ac5990-9f18-4677-a991-8d1c90020525
-- title:
--   Lemma 3 — clipped approximation with fewer than gamma inverse square signed tests
-- statement:
--   Let $V$ be a finite vertex set, $T$ a finite nonempty family of real pair functions taking values in $[-1,1]$, and $G,H$ arbitrary weighted graphs on $V$. Fix any real $0<\gamma<1$. There are an integer $t$ and pair functions $B_1,\ldots,B_t$ such that
--
--   $$0\le t<\gamma^{-2},\qquad B_j\in T\cup(-T),$$
--
--   and the actual clipped graph
--
--   $$W=\operatorname{clip}\left(G+\gamma\sum_{j=1}^t B_j\right)$$
--
--   satisfies $\|H-W\|_T\le\gamma$. The bound is strict, $t=0$ is allowed, and the starting graph can have arbitrary real edge weights. No restriction to the tester-derived family is made. This is the approximation statement used to obtain finite descriptions.
--
--   Differences from the source:
--   - encoding: graphs on arbitrary finite vertex sets and uniform unordered-pair or ordered-injective-tuple averages → graphs on Fin n, increasing endpoint pairs, and exact finite averages; reason: enumeration and relabeling preserve every finite instance and the source normalization
--   - generalization: pair inner products are introduced for orders at least two → all finite orders, with the empty-pair mean defined as zero; reason: at orders zero and one the weighted graph is unique, every correlation is zero, and t=0 supplies exactly the stated conclusion
-- source:
--   Gaia Carenini, Cameron Seth, STOC 2027 submission #583 (October 2026), Lemma 3, p. 14 (PDF 14)

import Definitions.Def_TestingEstimation_Dense_Objective

noncomputable section

namespace TestingEstimation.Dense

theorem clipped_boosting {n : ℕ} (T : Finset (PairFunction n)) (hT : T.Nonempty)
    (hbounded : ∀ A ∈ T, ∀ e, -1 ≤ A e ∧ A e ≤ 1)
    (G H : WGraph n) (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 1) :
    ∃ t : ℕ, (t:ℝ) < (γ^2)⁻¹ ∧ ∃ B : Fin t → PairFunction n,
      (∀ j, B j ∈ T ∨ -B j ∈ T) ∧
      correlation T (values H - values (boosted G γ B)) ≤ γ := by sorry

end TestingEstimation.Dense
