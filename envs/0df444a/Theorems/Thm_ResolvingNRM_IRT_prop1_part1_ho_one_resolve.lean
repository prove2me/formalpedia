-- Prove2me | Theorems.Thm_ResolvingNRM_IRT_prop1_part1_ho_one_resolve
-- name    : ResolvingNRM.IRT.prop1_part1_ho_one_resolve
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-07T03:22:54.272267+00:00
-- url     : https://prove2.me/theorems/88e878f3-3083-4d10-bd17-827c182615ff
-- title:
--   Proposition 1(1), p. 16 — HO$^1$ (one re-solve at $T - T^{5/6}$) loses $O(T e^{-\kappa T^{1/6}})$ against the hindsight optimum
-- statement:
--   Consider the network revenue-management model with $n$ customer classes arriving as independent Poisson processes of rates $\lambda_j > 0$, revenues $r_j \ge 0$ and a nonnegative bill-of-materials matrix $A$. Let $\mathrm{HO}^1$ be the policy that, over $[0, t^*_1)$ with $t^*_1 = T - T^{5/6}$, accepts class-$j$ customers (when capacity allows) with the thresholded probabilities of Algorithm 3 computed from the DLP solution $x^* = \mathrm{sel}(C/T)$, namely $0$ if $x^*_j < \lambda_j T^{-1/4}$, $1$ if $x^*_j > \lambda_j(1 - T^{-1/4})$ and $x^*_j/\lambda_j$ otherwise, and then from $t^*_1$ on follows the hindsight optimum of the remaining horizon $T^{5/6}$ with the remaining capacity.
--
--   **Part 1 of Proposition 1.** There are constants $\kappa > 0$ and $M$, depending only on $(\lambda, r, A)$, such that for every choice of optimal DLP solutions (selector), every $T \ge 1$ and every capacity vector $C \ge 0$,
--   $$v^{\mathrm{HO}}(T, C) - v^{\mathrm{HO}^1}(T, C) \le M\, T\, e^{-\kappa T^{1/6}} .$$
--
--   In the paper $\kappa = \lambda_{\min}/(27(\alpha|J_\lambda| + 1)^2)$, where $J_\lambda = \{j : x^*_j = \lambda_j\}$ and $\alpha$ depends only on $A$; since $|J_\lambda| \le n$ the constant can be taken uniform over the DLP solution, which is why $\kappa$ is quantified before the selector, $T$ and $C$. This is the first item of Proposition 1 (p. 16), proved in Appendix B.2, Eqs. (14)-(23), using Lemma 5 (stability of the hindsight LP, Reiman and Wang 2008, Thm 4.2) and Lemma 6 (the bound on $\mathbb P(E^c)$). The second item of Proposition 1 follows from this one together with Proposition 5, as in Eqs. (19)-(20).
-- source:
--   Bumpensanti, Wang, A Re-solving Heuristic with Uniformly Bounded Loss for Network Revenue Management, arXiv:1802.06192v3, Proposition 1 item 1, p. 16; proof in Appendix B.2, pp. 30-32, Eqs. (14)-(23)

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Definitions.Def_ResolvingNRM_IRT_Model

open RLPBidPrice.Unbiased Matrix

namespace ResolvingNRM.IRT

theorem prop1_part1_ho_one_resolve {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : ∀ j, 0 ≤ r j) (hA : ∀ l j, 0 ≤ A l j) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ M : ℝ, ∀ sel : (Fin m → ℝ) → (Fin n → ℝ), IsDLPSelector A r lam sel →
      ∀ T : ℝ, 1 ≤ T → ∀ C : Fin m → ℝ, 0 ≤ C →
        hindsightValue A r lam T C - hoValue A r lam sel 1 T C ≤
          M * T * Real.exp (-κ * T ^ (1 / 6 : ℝ)) := by sorry

end ResolvingNRM.IRT
