-- Prove2me | Theorems.Thm_TRSHolderKL_lemma_3_10
-- name    : TRSHolderKL.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:53:34.684593+00:00
-- url     : https://prove2.me/theorems/e2a82891-dd4c-4285-8bfd-fbe96ca06e08
-- title:
--   Lemma 3.10 — projections onto $S_0$ in hard case 2 (ii) (corrected: $\Pi_C(x)$ taken inside $C$)
-- statement:
--   Let $A$ be a nonzero real symmetric $n\times n$ matrix ($n\ge2$) and $b\in\mathbb R^n$ in hard case 2 (ii), and let $\bar x=(A-\lambda_1I)^\dagger b$. Given $x\in\mathbb R^n$, let $x_1=\Pi_{S_1}(x)$ be the projection of $x$ onto the convex set $S_1$. Then:
--   1. if $x_1=\bar x$, then $\Pi_{S_0}(x)=S_0$ and
--   $$
--   \operatorname{dist}(x,S_0)=\sqrt{\|x-\bar x\|^2+1-\|\bar x\|^2};
--   $$
--   2. if $x_1\ne\bar x$, then $v_1=(x_1-\bar x)/\|x_1-\bar x\|\in\mathrm{Null}(A-\lambda_1I)$, and $\Pi_{S_0}(x)=\{\bar x+t_0v_1\}$ for some $t_0\ge\|x_1-\bar x\|$ with $\|\bar x+t_0v_1\|=1$.
--
--   Here $\Pi_C(x)$ is the set of points of $C$ nearest to $x$. The lemma relates the nonconvex set $S_0$ (a sphere piece) to the convex set $S_1$ (a ball piece) in the one hard case where they differ.
--
--   Differences from the source:
--   - encoding: ℝⁿ; an n × n nonzero real symmetric matrix A; λ₁ the smallest eigenvalue → EuclideanSpace ℝ (Fin n); A : Matrix with A.IsHermitian and A ≠ 0 acting by Matrix.toEuclideanLin; lam1 A the least element of the real spectrum; reason: Lean conventions; the same instances
--   - encoding: λ*, the Lagrange multiplier in the case definitions of Table 1 → some x* ∈ S₀ and λ* satisfy the KKT conditions of p.4; reason: for λ₁ < 0 the multiplier is the same for every optimal solution, so this is the table's λ*
--   - correction: Π_C(x) = {v ∈ ℝⁿ | ‖x − v‖ = dist(x, C)} (Notation, p.3) → Π_C(x) = {v ∈ C | ‖x − v‖ = dist(x, C)} (projSet); reason: read literally, item 1 is false: n = 2, A = diag(−1, 0), b = 0 is hard case 2 (ii) (λ₁ = −1, x̄ = 0, S₀ = {±e₁}, λ* = 1); at x = 0, x₁ = 0 = x̄ and the literal Π_{S₀}(0) is the whole unit circle, not S₀
--   - encoding: x₁ := Π_{S₁}(x) → any x₁ ∈ projSet S₁ x (a hypothesis); reason: S₁ is nonempty, closed and convex, so its nearest point to x exists and is unique; the hypothesis names it
--   - encoding: Π_{S₀}(x) = x̄ + t₀v₁ (written as a point) → projSet (S0 A b) x = {x̄ + t₀v₁} (a singleton set); reason: Π_C is set-valued (Notation, p.3), and the proof on p.9 says that Π_{S₀}(x) is a singleton
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, Lemma 3.10, p.8; Notation, p.3

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_S0
import Definitions.Def_TRSHolderKL_S1
import Definitions.Def_TRSHolderKL_projSet
import Definitions.Def_TRSHolderKL_shiftLin
import Definitions.Def_TRSHolderKL_xbar
import Definitions.Def_TRSHolderKL_HardCase2ii

open scoped InnerProductSpace
open RBMSensitivity (E)

namespace TRSHolderKL

/-- Lemma 3.10, Jiang and Li, arXiv:1911.11955v2, p.8. In hard case 2 (ii), let `x ∈ ℝⁿ` and
let `x₁ = Π_{S₁}(x)` be the projection of `x` onto the convex set `S₁`. Then
1. if `x₁ = x̄`, then `Π_{S₀}(x) = S₀` and `dist(x, S₀) = √(‖x − x̄‖² + 1 − ‖x̄‖²)`;
2. if `x₁ ≠ x̄`, then `Π_{S₀}(x) = {x̄ + t₀v₁}` with `v₁ = (x₁ − x̄)/‖x₁ − x̄‖ ∈ Null(A − λ₁I)`
   and some `t₀ ≥ ‖x₁ − x̄‖` such that `‖x̄ + t₀v₁‖ = 1`.

**Formalization Note.** `x₁` is any nearest point of `S₁` to `x` (there is exactly one, `S₁`
being nonempty, closed and convex). `Π_C(x)` is the set of nearest points of `C` (`projSet`). -/
theorem lemma_3_10 {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hA0 : A ≠ 0) (b : E n) (hcase : HardCase2ii A b) (x x1 : E n)
    (hx1 : x1 ∈ projSet (S1 A b) x) :
    (x1 = xbar A b →
      projSet (S0 A b) x = S0 A b ∧
      Metric.infDist x (S0 A b) = Real.sqrt (‖x - xbar A b‖ ^ 2 + 1 - ‖xbar A b‖ ^ 2)) ∧
    (x1 ≠ xbar A b →
      ‖x1 - xbar A b‖⁻¹ • (x1 - xbar A b) ∈ LinearMap.ker (shiftLin A) ∧
      ∃ t0 : ℝ, ‖x1 - xbar A b‖ ≤ t0 ∧
        ‖xbar A b + t0 • (‖x1 - xbar A b‖⁻¹ • (x1 - xbar A b))‖ = 1 ∧
        projSet (S0 A b) x = {xbar A b + t0 • (‖x1 - xbar A b‖⁻¹ • (x1 - xbar A b))}) := by sorry

end TRSHolderKL
