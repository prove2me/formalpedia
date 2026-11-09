-- Prove2me | Theorems.Thm_TestingEstimation_Dense_multilinear_rounding
-- name    : TestingEstimation.Dense.multilinear_rounding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:27.770242+00:00
-- url     : https://prove2.me/theorems/d3f21ea0-02df-462d-bf9f-6f7722cc5bc7
-- title:
--   Fact 1 — independent rounding and equality of attained minima
-- statement:
--   Let $V$ have finite order $n$, and let $g$ be any real-valued function on its full real weighted-graph cube, affine in each edge weight separately. For every weighted graph $W$,
--
--   $$g(W)=\mathbb E\,g(\mathcal G(W)).$$
--
--   Here $\mathcal G(W)$ independently rounds each edge with its specified probability. Consequently,
--
--   $$\min_{W\in\mathcal W_V}g(W)=\min_{J\in\mathcal G_V}g(J).$$
--
--   Both minima are attained; this is included explicitly in the statement. Orders zero and one have their unique empty graph and are included. This fact justifies exact weighted relaxations without an additional regularity hypothesis on $g$.
--
--   Differences from the source:
--   - encoding: graphs on arbitrary finite vertex sets and uniform unordered-pair or ordered-injective-tuple averages → graphs on Fin n, increasing endpoint pairs, and exact finite averages; reason: enumeration and relabeling preserve every finite instance and the source normalization
--   - encoding: minimum or maximum → real infimum or supremum together with an explicit IsLeast or IsGreatest conclusion; reason: the conclusion includes attainment and excludes a replacement by a merely unattained extremal value
-- source:
--   Gaia Carenini, Cameron Seth, STOC 2027 submission #583 (October 2026), Fact 1, p. 8 (PDF 8)

import Definitions.Def_TestingEstimation_Dense_Objective

noncomputable section

namespace TestingEstimation.Dense

theorem multilinear_rounding {n : ℕ} (g : WGraph n → ℝ) (hg : Multiaffine g) :
    (∀ W, g W = roundingExpectation W (fun J => g (weighted J))) ∧
    sInf (Set.range g) = sInf (Set.range (fun J : Graph n => g (weighted J))) ∧
    IsLeast (Set.range g) (sInf (Set.range g)) ∧
    IsLeast (Set.range (fun J : Graph n => g (weighted J)))
      (sInf (Set.range (fun J : Graph n => g (weighted J)))) := by sorry

end TestingEstimation.Dense
