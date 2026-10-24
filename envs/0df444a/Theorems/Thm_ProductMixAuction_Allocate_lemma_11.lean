-- Prove2me | Theorems.Thm_ProductMixAuction_Allocate_lemma_11
-- name    : ProductMixAuction.Allocate.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:57.184209+00:00
-- url     : https://prove2.me/theorems/09d222f7-8531-4236-9530-9502473246d1
-- title:
--   Lemma 11 (time bound not modelled), p. 19 — NonMarginals returns a reduction and keeps G_A
-- statement:
--   Let $\mathcal A$ be an allocation problem (Definition 4) and let $\mathcal A'$ be the output of NonMarginals (Algorithm 3), which removes every non-marginal bid, adds its weight to its bidder's partial allocation on the good it demands and subtracts it from the residual supply. Then $\mathcal A'$ is a valid reduction of $\mathcal A$ (an allocation problem whose solutions are solutions of $\mathcal A$), and the marginal bids graphs agree:
--   $$G_{\mathcal A}=G_{\mathcal A'} .$$
--
--   ALLOCATE calls NonMarginals at the start and at the end of every iteration; the lemma says that this never loses a solution and never changes the graph that measures progress.
--
--   Differences from the source:
--   - encoding: in linear time → no running-time clause; reason: no machine model is formalized; the procedure is a single pass over the bids by construction
-- source:
--   Baldwin, Goldberg, Klemperer, Lock, Solving Strong-Substitutes Product-Mix Auctions, arXiv:1909.07313v3, p. 19, Lemma 11

import Mathlib
import Definitions.Def_ProductMixAuction_Allocate_Algorithm

namespace ProductMixAuction.Allocate

theorem lemma_11 {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J] (A : AllocProblem n J)
    (hA : IsAllocProblem A) :
    IsReduction (nonMarginals A) A ∧ edges (nonMarginals A) = edges A := by sorry

end ProductMixAuction.Allocate
