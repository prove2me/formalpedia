-- Prove2me | Theorems.Thm_ProductMixAuction_Allocate_lemma_18
-- name    : ProductMixAuction.Allocate.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:09.439493+00:00
-- url     : https://prove2.me/theorems/17616f30-d51c-41f9-bc07-051a21fb1db5
-- title:
--   Lemma 18 (time bound not modelled), p. 22 — ShiftProjectUnshift returns a reduction
-- statement:
--   Let $\mathcal A$ be an allocation problem with integral bids and an integral price $p$, let $i^*$ be a cycle-link good of a multi-bidder cycle of $G_{\mathcal A}$ and $j^*$ the label of one of its edges in that cycle, and let the SFM oracle return a minimiser of every submodular set function. Then the output $\mathcal A'$ of ShiftProjectUnshift (Algorithm 5) on $(\mathcal A,i^*,j^*)$ — shift $j^*$'s bids by $\tfrac1{10}e^{i^*}$, move to the price $p^\varepsilon$ found by SFM, project every bid list w.r.t. $p^\varepsilon$, unshift and return to $p$ — is a valid reduction of $\mathcal A$.
--
--   Unlike the other two procedures, ShiftProjectUnshift allocates nothing; the lemma says it never loses a solution.
--
--   Differences from the source:
--   - encoding: in time O(T(n) + n|ℬ|) → no running-time clause; the procedure makes exactly two oracle calls by construction; reason: no machine model is formalized
--   - reading: Lemma 18 states no integrality → integral bids and integral price p; reason: Algorithm 5 relies on Lemma 13 and Proposition 14, which assume integral bids and prices; ALLOCATE's bids stay integral
--   - reading: cycle-link good i* (Algorithm 5's input) → i* any cycle-link good, including the reject good 0; reason: Algorithm 5 read literally: the shift then sets the reject entry of j*'s bids to 1/10
-- source:
--   Baldwin, Goldberg, Klemperer, Lock, Solving Strong-Substitutes Product-Mix Auctions, arXiv:1909.07313v3, p. 22, Lemma 18, Algorithm 5

import Mathlib
import Definitions.Def_ProductMixAuction_Allocate_Algorithm

namespace ProductMixAuction.Allocate

theorem lemma_18 {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J] (A : AllocProblem n J)
    (hA : IsAllocProblem A)
    (hbint : ∀ j, ∀ b ∈ A.B j, ∀ k, ∃ z : ℤ, b.v k = z)
    (hpint : ∀ i, ∃ z : ℤ, A.p i = z)
    (istar : Fin (n + 1)) (jstar : J) (hcyc : IsCycleLink A istar jstar)
    (sfm : SFMOracle n) (hsfm : SfmAdmissible sfm) :
    IsReduction (shiftProjectUnshift sfm A istar jstar) A := by sorry

end ProductMixAuction.Allocate
