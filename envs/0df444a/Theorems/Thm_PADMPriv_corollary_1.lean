-- Prove2me | Theorems.Thm_PADMPriv_corollary_1
-- name    : PADMPriv.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:08:28.459121+00:00
-- url     : https://prove2.me/theorems/78687ad0-ce8e-4e0b-8a97-12994d2b6170
-- title:
--   Corollary 1 — $(x_\star,y_\star)$ is feasible with objective gap at most $\Delta_\beta+(L_F\|V\|_2+L_g\|U\|_2)^2/(8\beta)$; $\Delta_\beta=0$ under (19)
-- statement:
--   Let $F$, $g$ be convex, $\beta>0$, and let $A$, $B$ have full row rank, $V=A^\top(AA^\top)^{-1}$, $U=B^\top(BB^\top)^{-1}$. Let $(\hat x_\star,\hat y_\star)$ minimize the penalized problem (16), and set
--   $$
--   u_\star = \frac{A\hat x_\star-B\hat y_\star+c}{2},\qquad x_\star = Vu_\star,\qquad y_\star = U(c-u_\star).
--   $$
--   Let $(x^{\rm opt},y^{\rm opt})$ be an optimal solution of model (1). Assume $F$ is $L_F$-Lipschitz on the segment between $VA\hat x_\star$ and $x_\star$, and $g$ is $L_g$-Lipschitz on the segment between $UB\hat y_\star$ and $y_\star$ ($L_F,L_g\ge0$). Then $(x_\star,y_\star)$ is feasible, $Ax_\star+By_\star=c$, and
--   $$
--   0\le F(x_\star)+g(y_\star)-F(x^{\rm opt})-g(y^{\rm opt}) \le \Delta_\beta + \frac{(L_F\|V\|_2+L_g\|U\|_2)^2}{8\beta}, \tag{17}
--   $$
--   where $\Delta_\beta := F(VA\hat x_\star)-F(\hat x_\star)+g(UB\hat y_\star)-g(\hat y_\star)$ (18). If moreover $F(VAx)\le F(x)$ for all $x$ and $g(UBy)\le g(y)$ for all $y$ (19), then $\Delta_\beta=0$.
--
--   The corollary turns a fixed point of $T_F$ into a feasible point with an $O(1/\beta)$ objective gap.
--
--   **Formalization Note** $u_\star$, $x_\star$, $y_\star$ and $\Delta_\beta$ are variables bound by their defining equations.
--
--   Differences from the source:
--   - encoding: u⋆, x⋆, y⋆, Δ_β as defined quantities → variables with hypotheses equating them to their definitions; reason: names for the paper's values; same instances
--   - encoding: L_F- and L_g-Lipschitz constants → hypotheses 0 ≤ L_F, 0 ≤ L_g; reason: a Lipschitz constant is nonnegative; same instances
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Corollary 1, pp.7–8 (proof A.2, pp.20–21)

import Mathlib
import Definitions.Def_PADMPriv_pinvRight
import Definitions.Def_LiqPremiaEq_opNorm
import Definitions.Def_PADMPriv_IsOptimal
import Definitions.Def_PADMPriv_IsPenalizedMin

namespace PADMPriv

/-- Corollary 1 of Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), pp.7–8 (proof A.2, pp.20–21). Let `(x̂⋆, ŷ⋆)` minimize
(16), `u⋆ = (A x̂⋆ − B ŷ⋆ + c)/2`, `x⋆ = V u⋆`, `y⋆ = U(c − u⋆)`, and let `(x_opt, y_opt)` be an
optimal solution of model (1), with `A`, `B` of full row rank. If `F` is `L_F`-Lipschitz on the
segment between `V A x̂⋆` and `x⋆` and `g` is `L_g`-Lipschitz on the segment between `U B ŷ⋆` and
`y⋆`, then `(x⋆, y⋆)` is feasible and
`0 ≤ F(x⋆) + g(y⋆) − F(x_opt) − g(y_opt) ≤ Δ_β + (L_F‖V‖₂ + L_g‖U‖₂)²/(8β)` (17), with
`Δ_β = F(V A x̂⋆) − F(x̂⋆) + g(U B ŷ⋆) − g(ŷ⋆)` (18); under (19), `Δ_β = 0`.

**Formalization Note** `u⋆`, `x⋆`, `y⋆`, `Δ_β` are variables bound by their defining equations.
`F`, `g` are real-valued convex and `β > 0` (p.7). Full row rank is `rank = m`. -/
theorem corollary_1 {m p l : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin l) ℝ)
    (c : EuclideanSpace ℝ (Fin m)) (F : EuclideanSpace ℝ (Fin p) → ℝ)
    (g : EuclideanSpace ℝ (Fin l) → ℝ) (hF : ConvexOn ℝ Set.univ F)
    (hg : ConvexOn ℝ Set.univ g) (β : ℝ) (hβ : 0 < β) (hA : A.rank = m) (hB : B.rank = m)
    (xh : EuclideanSpace ℝ (Fin p)) (yh : EuclideanSpace ℝ (Fin l))
    (hmin : IsPenalizedMin β F g A B c xh yh)
    (ustar : EuclideanSpace ℝ (Fin m))
    (hustar : ustar = (1 / 2 : ℝ) • (Matrix.toEuclideanLin A xh - Matrix.toEuclideanLin B yh + c))
    (xstar : EuclideanSpace ℝ (Fin p)) (hxstar : xstar = Matrix.toEuclideanLin (pinvRight A) ustar)
    (ystar : EuclideanSpace ℝ (Fin l))
    (hystar : ystar = Matrix.toEuclideanLin (pinvRight B) (c - ustar))
    (xopt : EuclideanSpace ℝ (Fin p)) (yopt : EuclideanSpace ℝ (Fin l))
    (hopt : IsOptimal F g A B c xopt yopt) (LF Lg : ℝ) (hLF : 0 ≤ LF) (hLg : 0 ≤ Lg)
    (hFLip : ∀ x ∈ segment ℝ (Matrix.toEuclideanLin (pinvRight A) (Matrix.toEuclideanLin A xh)) xstar,
      ∀ x' ∈ segment ℝ (Matrix.toEuclideanLin (pinvRight A) (Matrix.toEuclideanLin A xh)) xstar,
        |F x - F x'| ≤ LF * ‖x - x'‖)
    (hgLip : ∀ y ∈ segment ℝ (Matrix.toEuclideanLin (pinvRight B) (Matrix.toEuclideanLin B yh)) ystar,
      ∀ y' ∈ segment ℝ (Matrix.toEuclideanLin (pinvRight B) (Matrix.toEuclideanLin B yh)) ystar,
        |g y - g y'| ≤ Lg * ‖y - y'‖)
    (Δβ : ℝ)
    (hΔ : Δβ = F (Matrix.toEuclideanLin (pinvRight A) (Matrix.toEuclideanLin A xh)) - F xh +
      g (Matrix.toEuclideanLin (pinvRight B) (Matrix.toEuclideanLin B yh)) - g yh) :
    Matrix.toEuclideanLin A xstar + Matrix.toEuclideanLin B ystar = c ∧
      0 ≤ F xstar + g ystar - F xopt - g yopt ∧
      F xstar + g ystar - F xopt - g yopt ≤
        Δβ + (LF * LiqPremiaEq.opNorm (pinvRight A) + Lg * LiqPremiaEq.opNorm (pinvRight B)) ^ 2 / (8 * β) ∧
      ((∀ x, F (Matrix.toEuclideanLin (pinvRight A) (Matrix.toEuclideanLin A x)) ≤ F x) →
        (∀ y, g (Matrix.toEuclideanLin (pinvRight B) (Matrix.toEuclideanLin B y)) ≤ g y) →
          Δβ = 0) := by sorry

end PADMPriv
