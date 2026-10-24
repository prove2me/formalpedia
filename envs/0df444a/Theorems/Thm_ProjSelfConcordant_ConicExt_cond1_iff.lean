-- Prove2me | Theorems.Thm_ProjSelfConcordant_ConicExt_cond1_iff
-- name    : ProjSelfConcordant.ConicExt.cond1_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:58.105592+00:00
-- url     : https://prove2.me/theorems/1e0c3f8b-c12b-4aed-b67e-3f614c9aa810
-- title:
--   §2, p. 5 — condition (1) of Definition 1.4 for f iff condition (1) of Definition 1.1 for F on K
-- statement:
--   Let $D\subset\mathbb R^n$ be open and convex, $f$ a $C^3$ function on $D$, $\nu\ge2$, $K=\{(t,x)\mid t>0,\ t^{-1}x\in D\}$ and $F(t,x)=\nu(-\log t+f(t^{-1}x))$. Then
--   $$f''(x)-f'(x)f'(x)^{T}\succ0\ \ \forall x\in D \quad\Longleftrightarrow\quad F''(y)\succ0\ \ \forall y\in K.$$
--
--   This is the half of Theorem 1.5 that concerns positive definiteness: the affine metric of $f$ is positive definite exactly when the Hessian of its logarithmically homogeneous extension is.
--
--   **Formalization Note** Positive definiteness of a symmetric form is positivity of its quadratic form on nonzero vectors.
-- source:
--   Hildebrand, Projectively Self-Concordant Barriers, arXiv:1909.01883v2, p. 5, §2, proof of Theorem 1.5 (the two discriminant arguments)

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting

namespace ProjSelfConcordant.ConicExt

/-- §2, p. 5: condition (1) of Definition 1.4 for `f` on `D` holds if and only if condition (1)
of Definition 1.1 holds for `F(t, x) = ν(−log t + f(t⁻¹x))` on the conic extension `K`. -/
theorem cond1_iff {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (hDo : IsOpen D) (hDc : Convex ℝ D)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiffOn ℝ 3 f D) (ν : ℝ) (hν : 2 ≤ ν) :
    ProjCond1 D f ↔ AffCond1 (conicExt D) (homExt ν f) := by sorry

end ProjSelfConcordant.ConicExt
