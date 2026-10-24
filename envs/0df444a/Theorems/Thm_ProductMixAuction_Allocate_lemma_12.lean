-- Prove2me | Theorems.Thm_ProductMixAuction_Allocate_lemma_12
-- name    : ProductMixAuction.Allocate.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:19.699258+00:00
-- url     : https://prove2.me/theorems/a1dce030-8c5c-4a2e-874f-20f42bad2f0c
-- title:
--   Lemma 12 (time bound not modelled), p. 20 — UnambiguousMarginals returns a valid reduction with strictly fewer edges
-- statement:
--   Let $\mathcal A$ be an allocation problem without non-marginal bids, and let $(I,j)$ be a demand cluster of $G_{\mathcal A}$ with at most one link good (the situation of p. 19). Let $\mathcal A'$ be the output of UnambiguousMarginals (Algorithm 4) on $(I,j)$. Then $\mathcal A'$ is a valid reduction of $\mathcal A$, and
--   $$|E(G_{\mathcal A'})|<|E(G_{\mathcal A})| .$$
--
--   Together with Lemma 17 this is the progress measure of ALLOCATE: each iteration deletes at least one labelled edge of the marginal bids graph.
--
--   Differences from the source:
--   - encoding: in time O(n|ℬʲ|) → no running-time clause; reason: no machine model is formalized
--   - reading: Lemma 12 states no hypotheses on A and (I, j) → A an allocation problem without non-marginal bids and (I, j) a demand cluster with at most one link good; reason: these are the standing assumptions of the paragraph introducing Algorithm 4 (p. 19) and its input line
-- source:
--   Baldwin, Goldberg, Klemperer, Lock, Solving Strong-Substitutes Product-Mix Auctions, arXiv:1909.07313v3, p. 20, Lemma 12; hypotheses from p. 19

import Mathlib
import Definitions.Def_ProductMixAuction_Allocate_Algorithm

namespace ProductMixAuction.Allocate

theorem lemma_12 {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J] (A : AllocProblem n J)
    (hA : IsAllocProblem A) (hmarg : ∀ j, ∀ b ∈ A.B j, IsMarginalBid b A.p)
    (I : Finset (Fin (n + 1))) (j : J) (hI : IsCluster A I j)
    (hlink : {i | i ∈ I ∧ IsLink A i}.Subsingleton) :
    IsReduction (unambiguousMarginals A I j) A ∧
      (edges (unambiguousMarginals A I j)).card < (edges A).card := by sorry

end ProductMixAuction.Allocate
