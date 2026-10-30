-- Prove2me | Theorems.Thm_ProductMixAuction_Allocate_lemma_18_nonMarginals_nonneg
-- name    : ProductMixAuction.Allocate.lemma_18_nonMarginals_nonneg
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-29T15:40:40.61999+00:00
-- url     : https://prove2.me/theorems/2c87cb7c-fc0d-4755-b603-c36b6a71d6c2
-- title:
--   Lemma 18 companion, p. 22 — NonMarginals after ShiftProjectUnshift keeps partial allocations non-negative
-- statement:
--   Let $A=[p,(\mathcal B^j)_{j\in J},(m^j)_{j\in J},r]$ be an allocation problem in the sense of Definition 4 (p. 15) with integral bids and an integral price $p$, in which every bid is marginal at $p$. This is the state in which Allocate calls ShiftProjectUnshift, right after NonMarginals. Let $i^*\in[n]_0$ be a cycle-link good with an incident cycle edge labelled $j^*$, and let the SFM oracle return a minimiser of every submodular set function. Let
--   $$A''=\mathrm{ShiftProjectUnshift}(A,i^*,j^*)$$
--   be the output of Algorithm 5 (p. 22), and let $\mathrm{NonMarginals}(A'')$ be the output of the NonMarginals call that follows it in the same loop iteration of Algorithm 1 (p. 14). Then the partial allocations of $\mathrm{NonMarginals}(A'')$ are non-negative:
--   $$m'^j_i\ \ge\ 0\qquad\text{for all } j\in J,\ i\in[n]_0 .$$
--
--   Algorithm 1 tacitly needs this so that the problem obtained after each loop iteration is again an allocation problem: Definition 4 requires $m^j\in\mathbb Z_+^{n+1}$. Lemma 11 alone does not guarantee it (see `ProductMixAuction.Allocate.lemma_11_nonneg`). The statement says that the bids which ShiftProjectUnshift turns non-marginal at $p$, and which NonMarginals then accepts, contribute a non-negative bundle to each bidder. This parallels the second claim of Lemma 13 (p. 21), that after the shift each bidder demands only bundles it already demanded at $p$.
--
--   **Formalization Note** The hypotheses are those of the milestone `ProductMixAuction.Allocate.lemma_18`, together with the marginality of all bids, which holds whenever Allocate calls ShiftProjectUnshift.
-- source:
--   Baldwin, Goldberg, Klemperer, Lock, Solving Strong-Substitutes Product-Mix Auctions, arXiv:1909.07313v3, p. 22, Algorithm 5 and Lemma 18 (ShiftProjectUnshift), p. 14 Algorithm 1 (loop: ShiftProjectUnshift followed by NonMarginals), p. 21 Lemma 13 (demand after shifting is a subset of demand at p), Definition 4 p. 15 (m^j in Z_+^{n+1})

import Mathlib
import Definitions.Def_ProductMixAuction_Allocate_Algorithm

namespace ProductMixAuction.Allocate

theorem lemma_18_nonMarginals_nonneg {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
    (A : AllocProblem n J) (hA : IsAllocProblem A)
    (hmarg : ∀ j, ∀ b ∈ A.B j, IsMarginalBid b A.p)
    (hbint : ∀ j, ∀ b ∈ A.B j, ∀ k, ∃ z : ℤ, b.v k = z)
    (hpint : ∀ i, ∃ z : ℤ, A.p i = z)
    (istar : Fin (n + 1)) (jstar : J) (hcyc : IsCycleLink A istar jstar)
    (sfm : SFMOracle n) (hsfm : SfmAdmissible sfm) :
    ∀ j k, 0 ≤ (nonMarginals (shiftProjectUnshift sfm A istar jstar)).m j k := by sorry

end ProductMixAuction.Allocate
