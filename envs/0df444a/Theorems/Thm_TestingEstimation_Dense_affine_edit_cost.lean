-- Prove2me | Theorems.Thm_TestingEstimation_Dense_affine_edit_cost
-- name    : TestingEstimation.Dense.affine_edit_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:35.797163+00:00
-- url     : https://prove2.me/theorems/b99e47c3-d021-48c9-b24a-3d212c378982
-- title:
--   Fact 3 — affine expected edit cost and agreement on graphs
-- statement:
--   Let $G$ be an ordinary graph on $n\ge2$ vertices and let $W$ range over all real weighted graphs on that vertex set. Write $\operatorname{cost}_G(W)=\mathbb E d(G,\mathcal G(W))$, where $d$ is normalized edit distance. With unordered-pair inner products,
--
--   $$0\le\operatorname{cost}_G(W)\le1,\qquad\operatorname{cost}_G(W)=\langle G,1\rangle+\langle W,1-2G\rangle.$$
--
--   The function $\operatorname{cost}_G$ is affine on the whole weighted cube, and for every ordinary graph $J$,
--
--   $$\operatorname{cost}_G(J)=d(G,J).$$
--
--   The affinity assertion concerns arbitrary convex mixtures of weighted graphs, not merely one-coordinate mixtures. This identifies the cost test needed alongside the tester derivatives.
--
--   Differences from the source:
--   - encoding: graphs on arbitrary finite vertex sets and uniform unordered-pair or ordered-injective-tuple averages → graphs on Fin n, increasing endpoint pairs, and exact finite averages; reason: enumeration and relabeling preserve every finite instance and the source normalization
-- source:
--   Gaia Carenini, Cameron Seth, STOC 2027 submission #583 (October 2026), Fact 3, p. 9 (PDF 9)

import Definitions.Def_TestingEstimation_Dense_Objective

noncomputable section

namespace TestingEstimation.Dense

theorem affine_edit_cost {n : ℕ} (hn : 2 ≤ n) (G : Graph n) :
    (∀ W : WGraph n, 0 ≤ cost G W ∧ cost G W ≤ 1 ∧
      cost G W = inner (fun e => bit (G e)) (fun _ => 1) +
        inner (values W) (fun e => 1 - 2 * bit (G e))) ∧
    AffineOnCube (cost G) ∧
    (∀ J : Graph n, cost G (weighted J) = editDistance G J) := by sorry

end TestingEstimation.Dense
