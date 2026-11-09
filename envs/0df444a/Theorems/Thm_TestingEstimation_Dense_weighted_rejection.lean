-- Prove2me | Theorems.Thm_TestingEstimation_Dense_weighted_rejection
-- name    : TestingEstimation.Dense.weighted_rejection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:35.131879+00:00
-- url     : https://prove2.me/theorems/7fe49c02-fea7-44ab-a9d3-318a9a728aa3
-- title:
--   Fact 2 — symmetry, multilinearity, rounding, and agreement on graphs
-- statement:
--   Fix integers $2\le s\le n$ and a symmetric rational rule $f:\mathcal G_s\to[0,1]\cap\mathbb Q$. Let $\phi(Y)=\mathbb E f(\mathcal G(Y))$ on weighted $s$-vertex graphs, and let $\operatorname{rej}(W)=\mathbb E_v\phi(W[v])$ on weighted $n$-vertex graphs. All expectations use the independent rounding law or uniform injective sampling, as appropriate. Then:
--
--   1. $\phi(Y\circ\sigma)=\phi(Y)$ for every permutation $\sigma$ of the $s$ sample positions.
--   2. Both $\phi$ and $\operatorname{rej}$ are affine in each edge coordinate separately.
--   3. Rounding commutes with rejection, and rejection agrees with the canonical rule on ordinary graphs:
--
--   $$\operatorname{rej}(W)=\mathbb E\operatorname{rej}(\mathcal G(W)),\qquad\operatorname{rej}(J)=\mathbb E_v f(J[v]).$$
--
--   All three assertions belong to this item. They supply the symmetry and multilinearity of the weighted tester extension.
--
--   Differences from the source:
--   - encoding: graphs on arbitrary finite vertex sets and uniform unordered-pair or ordered-injective-tuple averages → graphs on Fin n, increasing endpoint pairs, and exact finite averages; reason: enumeration and relabeling preserve every finite instance and the source normalization
--   - generalization: f is the symmetric rational canonical rule furnished by Proposition 1, including (N2) → f is any symmetric rational rule with values in [0,1], without an (N2) premise; reason: these analytic conclusions use only the rule table and its symmetry, so every source canonical rule is included
-- source:
--   Gaia Carenini, Cameron Seth, STOC 2027 submission #583 (October 2026), Fact 2, p. 9 (PDF 9)

import Definitions.Def_TestingEstimation_Dense_Objective

noncomputable section

namespace TestingEstimation.Dense

theorem weighted_rejection {s n : ℕ} (hs : 2 ≤ s) (hn : s ≤ n)
    (f : Rule s) (hf : SymmetricRule f) :
    (∀ (Y : WGraph s) (σ : Equiv.Perm (Fin s)),
      phi f (inducedW Y σ.toEmbedding) = phi f Y) ∧
    Multiaffine (phi f) ∧ Multiaffine (rejection (n := n) f) ∧
    (∀ W : WGraph n, rejection f W =
      roundingExpectation W (fun J => rejection f (weighted J))) ∧
    (∀ J : Graph n, rejection f (weighted J) = graphRej f J) := by sorry

end TestingEstimation.Dense
