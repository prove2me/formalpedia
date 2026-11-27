-- Prove2me | Theorems.Thm_StochSQP_Vanishing_Supplement_lemma_8
-- name    : StochSQP.Vanishing.Supplement.lemma_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T05:17:27.434794+00:00
-- url     : https://prove2.me/theorems/a6daa17e-412e-49eb-bca7-033d69bef054
-- title:
--   Lemma 8 (used in the proof of Theorem 1) — eventually constant positive merit
-- statement:
--   In a run satisfying Assumptions 1 and 3, suppose the Jacobians eventually have a uniform positive lower bound on all row singular values and $\|g_k-\nabla f(x_k)\|_2\le\kappa_g$ for every $k$, for some $\kappa_g>0$. Then
--   $$\exists k_\tau\in\mathbb N,\ \exists\tau_{\min}>0,\quad\tau_k=\tau_{\min}\quad(k\ge k_\tau).$$
--   This is eventual equality, not merely a positive lower bound, and does not specialize the gradients to exact ones. It supplies the positive-merit regime used by Theorem 1.
--
--   Differences from the source:
--   - generalization: stochastic algorithm context with unbiased finite-variance gradients and independent Hessians → a pathwise algorithm run with the stated deterministic bounds, without probability or moment premises; reason: the statement and proof of this lemma use only the pathwise rules and bounds; every stochastic realization satisfying the source assumptions specializes to this statement
--   - encoding: Euclidean matrix notation and sequence limits → finite Euclidean spaces, adjoints, varying-dimensional isometries, and Tendsto to zero; reason: these express the same vectors, norms, bases and full-sequence limits, including zero-dimensional spaces
-- source:
--   Berahas, Curtis, O'Neill & Robinson, arXiv:2106.13015v2, p. 14, Lemma 8

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Supplement_Geometry

namespace StochSQP.Vanishing.Supplement

open Filter
open scoped InnerProductSpace RealInnerProductSpace Topology

theorem lemma_8
    {n m : ℕ} (P : Problem n m) (A : Params) (R : Run n m)
    (X : Set (E n)) (κH ζH : ℝ)
    (hA : A.Valid) (hP : Assumption1 P A.L A.Γ X)
    (hx : ∀ k, R.x k ∈ X) (hH : Assumption3 P R κH ζH)
    (hrun : IsRun P A R)
    (hJ : EventualFullRank P R)
    (κg : ℝ) (hκg : 0 < κg) (hg : ∀ k, ‖R.g k - P.grad (R.x k)‖ ≤ κg) :
    ConstantMerit R := by sorry

end StochSQP.Vanishing.Supplement
