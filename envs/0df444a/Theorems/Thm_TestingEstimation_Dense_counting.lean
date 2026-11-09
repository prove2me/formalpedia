-- Prove2me | Theorems.Thm_TestingEstimation_Dense_counting
-- name    : TestingEstimation.Dense.counting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:31.693469+00:00
-- url     : https://prove2.me/theorems/9b180e98-481b-4c9b-87b8-d4f1a01bc865
-- title:
--   Lemma 2 — both counting inequalities
-- statement:
--   Put $s=a+2\ge2$, $K=\binom s2$, and suppose $n\ge4s$. Fix an ordinary graph $G$ and a symmetric rational rejection rule $f$ on $s$ vertices. Let $T(G)$ contain the cost test and all derivative tests, with every anchor graph and every vertex coloring admitted. For every pair of real weighted graphs $W,Z$,
--
--   $$|\operatorname{rej}(W)-\operatorname{rej}(Z)|\le2K\|W-Z\|_{T(G)},$$
--
--   $$|E_G(W)-E_G(Z)|\le(1+4K)\|W-Z\|_{T(G)}.$$
--
--   The seminorm is the maximum absolute unordered-pair correlation with the tests. The input order and its rule remain fixed throughout. These two inequalities state exactly which discrepancies the test family controls.
--
--   Differences from the source:
--   - encoding: graphs on arbitrary finite vertex sets and uniform unordered-pair or ordered-injective-tuple averages → graphs on Fin n, increasing endpoint pairs, and exact finite averages; reason: enumeration and relabeling preserve every finite instance and the source normalization
--   - encoding: sample size s at least 2 with anchors [3,s] → s=a+2 with anchors Fin a; reason: this bijective reindexing includes s=2 and its empty anchor set
--   - generalization: f is the symmetric rational canonical rule furnished by Proposition 1, including (N2) → f is any symmetric rational rule with values in [0,1], without an (N2) premise; reason: these analytic conclusions use only the rule table and its symmetry, so every source canonical rule is included
-- source:
--   Gaia Carenini, Cameron Seth, STOC 2027 submission #583 (October 2026), Lemma 2, p. 12 (PDF 12)

import Definitions.Def_TestingEstimation_Dense_Labels

noncomputable section

namespace TestingEstimation.Dense

theorem counting {a n : ℕ} (hn : 4*(a+2) ≤ n) (f : Rule (a+2))
    (hf : SymmetricRule f) (G : Graph n) (W Z : WGraph n) :
    |rejection f W - rejection f Z| ≤
      2 * (Nat.choose (a+2) 2 : ℝ) * correlation (tests f G) (values W - values Z) ∧
    |energy f G W - energy f G Z| ≤
      (1 + 4 * (Nat.choose (a+2) 2 : ℝ)) *
        correlation (tests f G) (values W - values Z) := by sorry

end TestingEstimation.Dense
