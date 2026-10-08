-- Prove2me | Theorems.Thm_TruncNewton_NegCurv_theorem_A_5
-- name    : TruncNewton.NegCurv.theorem_A_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:07:16.501948+00:00
-- url     : https://prove2.me/theorems/a757aa00-e95b-40cf-adb9-76a7ecda8103
-- title:
--   Theorem A.5, p. 210 — positive curvature on a conjugate basis of the full Krylov space forces H positive definite
-- statement:
--   Let $H$ be a symmetric linear operator on $\mathbb{R}^n$ with the standard inner product $(\cdot,\cdot)$, and for a real $\lambda$ let $E(\lambda,H)=\{v: Hv=\lambda v\}$ (A.21). Let $g\in\mathbb{R}^n$ have a nonzero projection on each eigenspace of $H$, and let $k$ be the number of distinct eigenvalues of $H$. Let $d_0,\dots,d_{k-1}$ be vectors such that
--
--   $$
--   (d_i,Hd_j)=0\ \ (i\ne j),\qquad (d_i,Hd_i)>0,\qquad i,j=0,1,\dots,k-1,
--   $$
--
--   and
--
--   $$
--   [d_0,\dots,d_{k-1}]=[g,Hg,\dots,H^{k-1}g]. \tag{A.23}
--   $$
--
--   Then $H$ is positive definite: $(v,Hv)>0$ for every $v\ne0$.
--
--   The theorem is the linear-algebra core of Theorem 2.4: an $H$-conjugate family with positive curvature that spans the Krylov space of a vector meeting every eigenspace certifies positive definiteness.
--
--   **Formalization Note** The vectors $d_i$ are arbitrary, not necessarily CG directions, as on the page. "$g$ has a nonzero projection on each eigenspace" is stated as: for every eigenvalue $\mu$ there is $v$ with $Hv=\mu v$ and $(g,v)\ne0$; for symmetric $H$ the orthogonal projection of $g$ onto $E(\mu,H)$ is nonzero exactly when $g$ is not orthogonal to $E(\mu,H)$. The number of distinct eigenvalues is the cardinality of $\{\mu : \exists v\ne0,\ Hv=\mu v\}$, a finite set for an operator on a finite-dimensional space. The page prints the range "$i\ne j,\ i=0,\dots,k-1$" in (A.22) with $j$'s range implicit; it is read as $i,j<k$.
-- source:
--   Dembo and Steihaug, Truncated-Newton algorithms for large-scale unconstrained optimization, Math. Programming 26 (1983), p. 210, Theorem A.5, (A.21)–(A.23)

import Mathlib
import Definitions.Def_TruncNewton_NegCurv_Setting

namespace TruncNewton.NegCurv

theorem theorem_A_5 {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hH : IsSelfAdjoint H)
    (g : EuclideanSpace ℝ (Fin n))
    (hg : ∀ μ : ℝ, (∃ v, v ≠ 0 ∧ H v = μ • v) → ∃ v, H v = μ • v ∧ inner ℝ g v ≠ 0)
    (k : ℕ) (hk : k = Set.ncard {μ : ℝ | ∃ v, v ≠ 0 ∧ H v = μ • v})
    (d : ℕ → EuclideanSpace ℝ (Fin n))
    (hconj : ∀ i j, i < k → j < k → i ≠ j → inner ℝ (d i) (H (d j)) = 0)
    (hpos : ∀ i, i < k → 0 < inner ℝ (d i) (H (d i)))
    (hspan : Submodule.span ℝ (d '' Set.Iio k) =
      Submodule.span ℝ ((fun i => (H ^ i) g) '' Set.Iio k)) :
    ∀ v, v ≠ 0 → 0 < inner ℝ v (H v) := by sorry

end TruncNewton.NegCurv
