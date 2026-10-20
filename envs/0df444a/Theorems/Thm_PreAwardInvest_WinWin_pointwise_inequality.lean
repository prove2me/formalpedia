-- Prove2me | Theorems.Thm_PreAwardInvest_WinWin_pointwise_inequality
-- name    : PreAwardInvest.WinWin.pointwise_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:14.746042+00:00
-- url     : https://prove2.me/theorems/1e7fda5a-eadb-4f7e-9271-8c212e764c88
-- title:
--   Proof of Theorem 2, p. 43 (PDF 44) — Σ A^BAI_i F/f = min F/f ≤ Σ A^BIA_i F/f, with Σ_i A^M_i = 1
-- statement:
--   Assume the standing assumptions, Assumption 1 and ex ante symmetric suppliers. Let $\beta^A$ be a symmetric Bayesian Nash equilibrium of BAI in which the common strategy is nondecreasing in cost, let $\beta^I$ be any strategy profile, and write $h(c_i)=F_i(c_i)/f_i(c_i)$. Then:
--   1. in BAI the winning probabilities sum to one at every bid vector, and in BIA the allocation probabilities sum to one at every bid and reduction vector (the buyer must transact);
--   2. for almost every cost vector $c$,
--   $$\sum_{i=1}^N A^{\mathrm{BAI}}_i(c)\,h(c_i)=\min_{1\le i\le N}h(c_i);$$
--   3. for every cost vector $c$ and realized reduction vector $t$,
--   $$\min_{1\le i\le N}h(c_i)\le\sum_{i=1}^N A^{\mathrm{BIA}}_i(c,t)\,h(c_i),$$
--   where $A^{\mathrm{BAI}}_i(c)$ is the award probability at the cost vector $c$, and $A^{\mathrm{BIA}}_i(c,t)$ is the award probability at $c,t$, averaging only over the random tie priority.
--
--   Part 2 says that in BAI the lowest-cost supplier wins almost surely; part 3 says that any allocation does at least as badly in the virtual-cost term. Integrated, they compare the two ex ante profits of Theorem 2.
--
--   **Formalization Note.** The paper prints $\sum_{i=1}^n$ with a lower-case $n$; it is $N$. Part 3 holds for every $c,t$ and every BIA profile, which implies the paper's almost-everywhere comparison. The BAI equilibrium is assumed symmetric and nondecreasing, as in Lemma 1 and §4.2; it is not assumed strictly increasing, since with one supplier the equilibrium bid is the constant $\bar c_1$.
-- source:
--   Chen, Beil & Duenyas, Procurement mechanisms with post-auction pre-award cost-reduction investigations, accepted manuscript (Operations Research 70(6), 2022; LBS Research Online eprint 2544), proof of Theorem 2, p. 43 (PDF 44)

import Mathlib
import Definitions.Def_PreAwardInvest_WinWin_Model

namespace PreAwardInvest.WinWin

open MeasureTheory

theorem pointwise_inequality {N : ℕ} [NeZero N] (P : Params N) (hS : P.Standing)
    (hA1 : Assumption1 P) (hsym : ExAnteSymmetric P) (τ : ℝ) (βI βA : Fin N → ℝ → ℝ)
    (hA : IsEqBAI P βA) (hAsym : ∀ i j, βA i = βA j)
    (hAmono : ∀ i, MonotoneOn (βA i) (Set.Icc (cLoI P i) (cHiI P i))) :
    (∀ b : Fin N → ℝ, ∑ i, winProbBAI P b i = 1) ∧
    (∀ b t : Fin N → ℝ, ∑ i, allocBIA P τ b t i = 1) ∧
    (∀ᵐ cv ∂(costVecLaw P),
      ∑ i, winProbBAI P (bidProfile βA cv) i * (Fi P i (cv i) / fi P i (cv i)) =
        Finset.univ.inf' Finset.univ_nonempty (fun i => Fi P i (cv i) / fi P i (cv i))) ∧
    (∀ cv t : Fin N → ℝ,
      Finset.univ.inf' Finset.univ_nonempty (fun i => Fi P i (cv i) / fi P i (cv i)) ≤
        ∑ i, allocBIA P τ (bidProfile βI cv) t i * (Fi P i (cv i) / fi P i (cv i))) := by sorry

end PreAwardInvest.WinWin
