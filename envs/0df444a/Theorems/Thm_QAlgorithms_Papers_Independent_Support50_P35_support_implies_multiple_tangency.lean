-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P35_support_implies_multiple_tangency
-- name    : QAlgorithms.Papers.Independent.Support50.P35.support_implies_multiple_tangency
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:38:11.553164+00:00
-- url     : https://prove2.me/theorems/55b726cc-6106-4686-97e8-5646b5e445e0
-- title:
--   Support forces common tangency and secant containment
-- statement:
--   Let \(M\subseteq\mathbb R^n\) be a \(C^1\) embedded manifold without boundary, including a nonsingular real variety. Let \(m>0\), and let \(H=\{y:a\cdot y=b\}\), with \(a\ne0\), bound a halfspace \(a\cdot y\leq b\) containing all of \(M\). Suppose \(x_1,\ldots,x_m\in M\cap H\). Then, with \(H_0=\ker(a\cdot -)\),
--
--   $$
--   \dim H_0=n-1,\qquad T_{x_j}M\subseteq H_0\ (1\leq j\leq m),\qquad
--   \operatorname{span}\{x_j-x_k:j\ne k\}\subseteq H_0.
--   $$
--
--   Consequently \(x_j+T_{x_j}M\subseteq H\) for every contact point: \(H\) is \(m\)-tangent. Tangent spaces are the spans of velocities of curves locally contained in the manifold. This is a necessary condition for support.
-- source:
--   Convex Hulls of Varieties and Entanglement Measures Based on the Roof Construction, arXiv:quant-ph/0402055v2, PDF p. 7, Proposition 2.6: support forces multiple tangency

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P35

noncomputable section

open scoped Matrix ComplexConjugate Topology Manifold

namespace QAlgorithms.Papers.Independent.Support50.P35

/-- PDF p.7, Proposition 2.6: support implies tangent-direction and secant-span
containment, hence multiple tangency. The manifold version is included. -/
theorem support_implies_multiple_tangency {n m : ℕ}
    (M : Set (Fin n → ℝ)) (d : ℕ) (hM : IsEmbeddedDim M d)
    (hm : 0 < m) (H : Hyperplane n) (x : Fin m → (Fin n → ℝ))
    (hsupport : ContainsInHalfspace H M) (hcontact : ∀ j, x j ∈ M ∩ H.points) :
    Module.finrank ℝ H.direction = n - 1 ∧
    (∀ j, tangentDirections M (x j) ≤ H.direction) ∧
    Submodule.span ℝ {v | ∃ j k : Fin m, j ≠ k ∧ v = x j - x k} ≤ H.direction ∧
    IsMTangent H M x ∧
    (∀ j v, v ∈ tangentDirections M (x j) → x j + v ∈ H.points) := by sorry

end QAlgorithms.Papers.Independent.Support50.P35

end
