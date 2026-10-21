-- Prove2me | Theorems.Thm_SubsetShrink_L1_eq_37
-- name    : SubsetShrink.L1.eq_37
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:35.103511+00:00
-- url     : https://prove2.me/theorems/455f92c7-539a-4226-94ee-acf47ac607da
-- title:
--   (37), p. 42 — basic inequality for the ℓ1-regularized best subset estimator
-- statement:
--   Let $y=f^*+\epsilon$, let $\hat\beta_1$ minimize the $\ell_1$-regularized subset objective over $B_0(k)$, and let $\beta\in B_0(k)$. Then
--
--   $$\|f^*-X\hat\beta_1\|_2^2+\lambda\|\hat\beta_1\|_1\le\|f^*-X\beta\|_2^2+2\epsilon^\top X(\hat\beta_1-\beta)+\lambda\|\beta\|_1.$$
--
--   This is the basic inequality used by both the slow and fast rate arguments.
--
--   **Formalization Note** The estimator is an argmin predicate, so the claim applies to every minimizer.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 42, (37)

import Mathlib
import Definitions.Def_SubsetShrink_L1_Model

namespace SubsetShrink.L1

/-- Equation (37), p. 42, for an arbitrary feasible comparator. -/
theorem eq_37 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (fstar ε : Fin n → ℝ) (k : ℕ) (lam : ℝ)
    (βhat β : Fin p → ℝ)
    (hbest : IsL1BestSubset X (fun i => fstar i + ε i) k lam βhat)
    (hβ : SubsetShrink.Events.l0 β ≤ k) :
    predictionError X fstar βhat + lam * SubsetShrink.Events.l1 βhat ≤
      predictionError X fstar β + 2 * SubsetShrink.Events.dot ε (X.mulVec (βhat - β)) + lam * SubsetShrink.Events.l1 β := by sorry

end SubsetShrink.L1
