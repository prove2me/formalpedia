-- Prove2me | Theorems.Thm_PADMPriv_theorem_3_1
-- name    : PADMPriv.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:08:52.543802+00:00
-- url     : https://prove2.me/theorems/f82b94d2-9609-446e-8dfd-f2d1a52d6167
-- title:
--   Theorem 3.1 — fixed points of $T_F$ are the points $(A\hat x_\star-B\hat y_\star+c)/2$ with $(\hat x_\star,\hat y_\star)$ minimizing (16)
-- statement:
--   Let $F:\mathbb R^p\to\mathbb R$ and $g:\mathbb R^l\to\mathbb R$ be convex, $A\in\mathbb R^{m\times p}$, $B\in\mathbb R^{m\times l}$, $c\in\mathbb R^m$, $\beta>0$, and let $T_F$ be the PADM operator (15). A point $u_\star\in\mathbb R^m$ is a fixed point of $T_F$ if and only if
--   $$
--   u_\star = \frac{A\hat x_\star - B\hat y_\star + c}{2}\quad\text{for some}\quad (\hat x_\star,\hat y_\star)\in\operatorname*{arg\,min}_{(x,y)}\Big\{F(x)+g(y)+\frac{\beta}{4}\|Ax+By-c\|_2^2\Big\}. \tag{16}
--   $$
--
--   The theorem identifies the limit points of PADM with the penalized problem (16); it yields a fixed point whenever (16) has a minimizer.
--
--   **Formalization Note** The proximal problems (13) for $F$ and $g$ are assumed to have minimizers at every input, so that $T_F$ is defined.
--
--   Differences from the source:
--   - encoding: the proximal operators P_{β,F,A}, P_{β,g,B} used as everywhere defined → hypotheses that (13) has a minimizer for F and for g at every input; reason: T_F is undefined otherwise; excludes only undefined cases
--   - generalization: full row rank of A and B (standing assumption, p.6) → not assumed; reason: the statement and its proof use only convexity and the proximal minimizers, never V or U; the source's case is an instance
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Theorem 3.1, p.7 (proof A.1, pp.19–20)

import Mathlib
import Definitions.Def_PADMPriv_padmOp
import Definitions.Def_PADMPriv_IsPenalizedMin

namespace PADMPriv

/-- Theorem 3.1 of Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), p.7 (proof A.1, pp.19–20): a point `u⋆ ∈ ℝᵐ` is a
fixed point of `T_F` if and only if `u⋆ = (A x̂⋆ − B ŷ⋆ + c)/2` for some minimizer `(x̂⋆, ŷ⋆)` of
the penalized problem (16).

**Formalization Note** `F` and `g` are real-valued convex functions and `β > 0` (Section 3.2,
p.7). The proximal problems (13) for `F` and `g` are assumed to have minimizers at every input,
so that `T_F` is defined (15). -/
theorem theorem_3_1 {m p l : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin l) ℝ)
    (c : EuclideanSpace ℝ (Fin m)) (F : EuclideanSpace ℝ (Fin p) → ℝ)
    (g : EuclideanSpace ℝ (Fin l) → ℝ) (hF : ConvexOn ℝ Set.univ F)
    (hg : ConvexOn ℝ Set.univ g) (β : ℝ) (hβ : 0 < β)
    (hFprox : ∀ u, ∃ x, IsProxMin β F A u x) (hgprox : ∀ v, ∃ y, IsProxMin β g B v y)
    (u : EuclideanSpace ℝ (Fin m)) :
    padmOp β F g A B c u = u ↔
      ∃ (xh : EuclideanSpace ℝ (Fin p)) (yh : EuclideanSpace ℝ (Fin l)),
        IsPenalizedMin β F g A B c xh yh ∧
          u = (1 / 2 : ℝ) • (Matrix.toEuclideanLin A xh - Matrix.toEuclideanLin B yh + c) := by sorry

end PADMPriv
