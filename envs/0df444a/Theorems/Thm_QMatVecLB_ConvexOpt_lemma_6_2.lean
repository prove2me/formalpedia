-- Prove2me | Theorems.Thm_QMatVecLB_ConvexOpt_lemma_6_2
-- name    : QMatVecLB.ConvexOpt.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:17:07.296443+00:00
-- url     : https://prove2.me/theorems/0607c833-95db-4f86-98e0-718d03b7f6d7
-- title:
--   Lemma 6.2 — Gaussian integration by parts off the singular set
-- statement:
--   Let $F$ be a bounded real function on real $n\times n$ matrices, $C^n$ on the invertible matrices. Define $R_{ij}F(B)=\left.\frac d{dt}F(B(I+tE_{ij}))\right|_{t=0}$. Suppose that every composition of at most $n$ such operators applied to $F$ is bounded on the invertible matrices. Then both integrands are integrable and
--
--   $$\mathbb E[q(B)F(B)]=\mathbb E[\det(B)\det(\partial_B)F(B)],$$
--
--   where $B$ has independent standard normal entries. No smoothness across the singular set is required. This is the integration identity for the inversion witness.
--
--   Differences from the source:
--   - encoding: real n by n matrices and their coordinate indices → RMat n with indices Fin n, the coordinate product measurable space and product Lebesgue measure; reason: this is the same finite-dimensional real matrix space; changing the index origin changes no instance
--   - encoding: expectations and witness integrals → the same integrals, with their integrability also asserted in the conclusion; reason: the source uses convergent integrals; convergence is made explicit rather than relying on the totalized nonintegrable Bochner integral
--   - encoding: bounded F with C^n regularity away from singular matrices → ContDiffOn on det != 0 and boundedness of every listed composition, with no global measurability premise; reason: continuity off the Gaussian-null singular set already gives almost-everywhere measurability; arbitrary values on that set are allowed by the source
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, Lemma 6.2, PDF p. 18 (printed p. 17).

import Mathlib
import Definitions.Def_QMatVecLB_ConvexOpt_Inversion

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
set_option autoImplicit false

namespace QMatVecLB.ConvexOpt
attribute [local instance] Classical.propDecidable

theorem lemma_6_2 (n : ℕ) (F : RMat n → ℝ)
    (hFb : boundedOn F Set.univ) (hFc : ContDiffOn ℝ n F (invertibles n))
    (hRb : ∀ indices : List (Fin n × Fin n), indices.length ≤ n →
      boundedOn (rightComposite indices F) (invertibles n)) :
    Integrable (fun B : RMat n => q B * F B) (GaussianMatrix.gaussianMatrix n n) ∧
    Integrable (fun B : RMat n => B.det * cayley F B) (GaussianMatrix.gaussianMatrix n n) ∧
    (∫ B : RMat n, q B * F B ∂GaussianMatrix.gaussianMatrix n n) =
      (∫ B : RMat n, B.det * cayley F B ∂GaussianMatrix.gaussianMatrix n n) := by sorry

end QMatVecLB.ConvexOpt
