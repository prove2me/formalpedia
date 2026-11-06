-- Prove2me | Theorems.Thm_PADMPriv_eq_75
-- name    : PADMPriv.eq_75
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:09:29.355947+00:00
-- url     : https://prove2.me/theorems/be73bf3b-bcd5-4e1e-8fb2-253b58787cc7
-- title:
--   Eq. (75) — $J$ is $\varrho_g$-strongly convex and its minimizer gives the unique optimal solution in $\mathrm{range}(A^\top)\times\mathrm{range}(B^\top)$
-- statement:
--   Let $A$, $B$ have full row rank, $F$ convex, $g$ convex and $B$-induced $\varrho_g$-strongly convex, and assume (19): $F(VAx)\le F(x)$ for all $x$ and $g(UBy)\le g(y)$ for all $y$. Then $J(u)=F(Vu)+g(U(c-u))$ is $\varrho_g$-strongly convex and there is $u^{\rm opt}\in\mathbb R^m$ such that
--
--   1. $J(u)-J(u^{\rm opt})\ge\frac{\varrho_g}{2}\|u-u^{\rm opt}\|_2^2$ for all $u$ (75) (so $u^{\rm opt}$ is the unique minimizer of $J$);
--   2. $(x^{\rm opt},y^{\rm opt})=(Vu^{\rm opt},U(c-u^{\rm opt}))$ is an optimal solution of model (1);
--   3. it is the only optimal solution of (1) in $\operatorname{range}(A^\top)\times\operatorname{range}(B^\top)$.
--
--   This fixes the reference solution against which Theorem 5.4 measures the private output.
--
--   **Formalization Note** Strong convexity is Mathlib's `StrongConvexOn` with modulus $\varrho_g$ (the $\frac{\varrho_g}{2}\|u-v\|^2$ convention).
--
--   Differences from the source:
--   - generalization: F the population loss under the conditions of Theorem 5.4 → any real-valued convex F with (19); reason: p.35 uses only convexity and (19); the population loss is convex and satisfies (19) under (25), so the source's case is an instance
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), A.16, Eq. (75), p.35

import Mathlib
import Definitions.Def_PADMPriv_restrictedObj
import Definitions.Def_PADMPriv_IsOptimal
import Definitions.Def_PADMPriv_IsInducedStronglyConvex

namespace PADMPriv

/-- A.16 and Eq. (75) of Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), p.35: if `A`, `B` have full row rank, `F` is
convex, `g` is convex and `B`-induced `ϱ_g`-strongly convex, and (19) holds
(`F(VAx) ≤ F(x)`, `g(UBy) ≤ g(y)` for all `x`, `y`), then `J(u) = F(Vu) + g(U(c − u))` is
`ϱ_g`-strongly convex with a unique minimizer `u_opt`; `(x_opt, y_opt) = (V u_opt, U(c − u_opt))` is
the unique optimal solution of model (1) in `range(Aᵀ) × range(Bᵀ)`; and
`J(u) − J(u_opt) ≥ (ϱ_g/2)‖u − u_opt‖₂²` for all `u` (75).

**Formalization Note** Strong convexity is Mathlib's `StrongConvexOn ℝ Set.univ ϱ_g`
(`J(θu + (1−θ)v) ≤ θJ(u) + (1−θ)J(v) − θ(1−θ)(ϱ_g/2)‖u − v‖²`). `range(Aᵀ)` is the range of
`x ↦ Aᵀx`. -/
theorem eq_75 {m p l : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin l) ℝ)
    (c : EuclideanSpace ℝ (Fin m)) (hA : A.rank = m) (hB : B.rank = m)
    (F : EuclideanSpace ℝ (Fin p) → ℝ) (g : EuclideanSpace ℝ (Fin l) → ℝ)
    (hF : ConvexOn ℝ Set.univ F) (hg : ConvexOn ℝ Set.univ g) (ϱg : ℝ)
    (hgsc : IsInducedStronglyConvex B ϱg g)
    (hF19 : ∀ x, F (Matrix.toEuclideanLin (pinvRight A) (Matrix.toEuclideanLin A x)) ≤ F x)
    (hg19 : ∀ y, g (Matrix.toEuclideanLin (pinvRight B) (Matrix.toEuclideanLin B y)) ≤ g y) :
    StrongConvexOn Set.univ ϱg (restrictedObj F g A B c) ∧
      ∃ uopt : EuclideanSpace ℝ (Fin m),
        (∀ u, ϱg / 2 * ‖u - uopt‖ ^ 2 ≤ restrictedObj F g A B c u - restrictedObj F g A B c uopt) ∧
        IsOptimal F g A B c (Matrix.toEuclideanLin (pinvRight A) uopt)
          (Matrix.toEuclideanLin (pinvRight B) (c - uopt)) ∧
        ∀ (x : EuclideanSpace ℝ (Fin p)) (y : EuclideanSpace ℝ (Fin l)),
          x ∈ LinearMap.range (Matrix.toEuclideanLin A.transpose) →
          y ∈ LinearMap.range (Matrix.toEuclideanLin B.transpose) →
          IsOptimal F g A B c x y →
            x = Matrix.toEuclideanLin (pinvRight A) uopt ∧
              y = Matrix.toEuclideanLin (pinvRight B) (c - uopt) := by sorry

end PADMPriv
