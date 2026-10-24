-- Prove2me | Theorems.Thm_ProductMixAuction_Allocate_lemma_17
-- name    : ProductMixAuction.Allocate.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:26.982598+00:00
-- url     : https://prove2.me/theorems/9a78b0dc-1e61-4d8e-b647-dec4dddc7aeb
-- title:
--   Lemma 17, p. 22 — ShiftProjectUnshift strictly reduces the edges of G_A
-- statement:
--   Under the hypotheses of Lemma 18 — $\mathcal A$ an allocation problem with integral bids and integral price, $i^*$ a cycle-link good of a multi-bidder cycle of $G_{\mathcal A}$, $j^*$ the label of one of its edges in that cycle, and an SFM oracle that minimises submodular set functions — let $\mathcal A'$ be the output of ShiftProjectUnshift (Algorithm 5). Then the marginal bids graph of $\mathcal A'$ has strictly fewer edges than that of $\mathcal A$:
--   $$|E(G_{\mathcal A'})|<|E(G_{\mathcal A})| .$$
--
--   Together with Lemma 12 this bounds the number of iterations of ALLOCATE by the number $|J|\binom{n+1}2$ of possible labelled edges.
--
--   Differences from the source:
--   - reading: Lemma 17 states no hypotheses (A′ is Algorithm 5's output on A) → A an allocation problem with integral bids and price, (i*, j*) a cycle-link good and an incident cycle label, an admissible SFM oracle; reason: the context of p. 22: the input of Algorithm 5 as called by ALLOCATE
--   - reading: cycle-link good i* (Algorithm 5's input) → i* any cycle-link good, including the reject good 0; reason: Algorithm 5 read literally: the shift then sets the reject entry of j*'s bids to 1/10
-- source:
--   Baldwin, Goldberg, Klemperer, Lock, Solving Strong-Substitutes Product-Mix Auctions, arXiv:1909.07313v3, p. 22, Lemma 17; proof p. 39

import Mathlib
import Definitions.Def_ProductMixAuction_Allocate_Algorithm

namespace ProductMixAuction.Allocate

theorem lemma_17 {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J] (A : AllocProblem n J)
    (hA : IsAllocProblem A)
    (hbint : ∀ j, ∀ b ∈ A.B j, ∀ k, ∃ z : ℤ, b.v k = z)
    (hpint : ∀ i, ∃ z : ℤ, A.p i = z)
    (istar : Fin (n + 1)) (jstar : J) (hcyc : IsCycleLink A istar jstar)
    (sfm : SFMOracle n) (hsfm : SfmAdmissible sfm) :
    (edges (shiftProjectUnshift sfm A istar jstar)).card < (edges A).card := by sorry

end ProductMixAuction.Allocate
