-- Prove2me | Theorems.Thm_SurrogateOps_Supplement_theorem_30
-- name    : SurrogateOps.Supplement.theorem_30
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:42:55.84966+00:00
-- url     : https://prove2.me/theorems/3a541a11-a6ca-4951-9ffc-d9355e123032
-- title:
--   Theorem 30, p.19 (corrected: hypotheses on $\tilde f_{2,\Delta}$ at the points the proof uses, constant without $\bar M^{N^f_2}$) — function accuracy of a composition at/near $x_0$
-- statement:
--   Let $f_1:\mathbb R^d\to\mathbb R^m$ be $C^1$, $f_2:\mathbb R^m\to\mathbb R$, $F=f_2\circ f_1$ and $\tilde F_\Delta=\tilde f_{2,\Delta}\circ\tilde f_{1,\Delta}$, with every $\tilde f_{2,\Delta}$ in $C^1$. Suppose $\{\tilde f_{1,\Delta}\}_{(0,\bar\Delta]}$ provides order-$N^f_1$ function accuracy of $f_1$ at (resp. near) $x_0$ with constant $\kappa^f_1(x_0)$, $N^f_1>0$, and let $N^f_F=\min\{N^f_1,N^f_2\}$ and
--
--   $$
--   K^f_F=M_{\nabla\tilde f_2}\,\kappa^f_1(x_0)\,\bar\Delta^{N^f_1-N^f_F}+\kappa^f_2\,\bar\Delta^{N^f_2-N^f_F}.
--   $$
--
--   1. (at) If $\{\tilde f_{2,\Delta}\}$ provides order-$N^f_2$ function accuracy of $f_2$ at $f_1(x_0)$ with constant $\kappa^f_2$, and $\|\nabla\tilde f_{2,\Delta}(y)\|\le M_{\nabla\tilde f_2}$ for all $y$ on the segment $[f_1(x_0),\tilde f_{1,\Delta}(x_0)]$, then $|F(x_0)-\tilde F_\Delta(x_0)|\le K^f_F\Delta^{N^f_F}$ for all $\Delta\in(0,\bar\Delta]$.
--   2. (near) If, for all $\Delta\in(0,\bar\Delta]$ and $x\in B_\Delta(x_0)$, $|f_2(f_1(x))-\tilde f_{2,\Delta}(f_1(x))|\le\kappa^f_2\Delta^{N^f_2}$ (with $N^f_2,\kappa^f_2\ge0$) and $\|\nabla\tilde f_{2,\Delta}(y)\|\le M_{\nabla\tilde f_2}$ on $[f_1(x),\tilde f_{1,\Delta}(x)]$, then $|F(x)-\tilde F_\Delta(x)|\le K^f_F\Delta^{N^f_F}$ for all such $\Delta$, $x$.
--
--   In particular $\{\tilde F_\Delta\}_{(0,\bar\Delta]}$ provides order-$N^f_F$ function accuracy of $F$ at (resp. near) $x_0$.
--
--   The printed theorem assumes the accuracy and the gradient bound of the outer models only at or near $f_1(x_0)$ and has the factor $\bar M_{\nabla f_1}(x_0)^{N^f_2}$ in front of $\kappa^f_2$; it is false in both respects. The statement above assumes exactly what the proof on p.19 uses.
--
--   **Formalization Note** Accuracy of $f_1$ uses the vector-valued predicates with the Euclidean norm of $\mathbb R^m$.
--
--   Differences from the source:
--   - encoding: f₁ : ℝ^d → ℝ^m, f₂ : ℝ^m → ℝ, the closed balls, classes of models of f₁ and f₂ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m), EuclideanSpace ℝ (Fin m) → ℝ, Metric.closedBall, maps ℝ → E → G used only on Set.Ioc 0 Δbar; accuracy of f₁ by the vector-valued predicates SurrogateOps.Supplement.Vec*; reason: Lean convention; the vector-valued predicates are Definition 1 with the norm of ℝ^m; same instances
--   - encoding: the gradient ∇f and its Euclidean norm → fderiv ℝ f with the operator norm of E →L[ℝ] ℝ; reason: on EuclideanSpace the two norms agree by Riesz representation; same instances
--   - encoding: provides order-N accuracy: ∃ κ ≥ 0 → the constant κ is an explicit argument of the predicate, with 0 ≤ N and 0 ≤ κ as clauses; the order clause of the conclusion is ∃ κ; reason: a universally quantified κ in a hypothesis is the same as an existential one; the conclusion's κ depends on neither Δ nor x
--   - encoding: min{…} of finitely many orders → nested binary min of the reals; reason: same value
--   - encoding: the constant K(x₀) → a variable fixed by an equation hypothesis (or written out in the conclusion); reason: same as the page's "Let" and "where"
--   - encoding: {f̃_{2,Δ}}_{(0,Δ̄]} ⊆ C¹ → ContDiff ℝ 1 (fm₂ Δ) for every Δ ∈ (0, Δ̄]; reason: same instances
--   - correction: {‖∇f̃_{2,Δ}‖}_{(0,Δ̄]} is uniformly bounded at/near f₁(x₀) by M_{∇f̃₂}(f₁(x₀)) → ‖∇f̃_{2,Δ}(y)‖ ≤ M_{∇f̃₂} for every y on the segment [f₁(x), f̃_{1,Δ}(x)], with x = x₀ in case (i) and every x ∈ B_Δ(x₀) in case (ii); reason: false as printed (d = m = 1, x₀ = 0, f₂ = 0): in case (i) f₁ = 0, f̃_{1,Δ} = Δ, f̃_{2,Δ}(y) = y²/Δ³ have N^f_1 = 1, ∇f̃_{2,Δ}(0) = 0, but error 1/Δ at x₀; in case (ii) f₁ = f̃₁ = 2x (or f₁ = 0, f̃_{1,Δ} = x + 2Δ) with f̃_{2,Δ}(y) = max(0, y² − Δ²)²/Δ⁵, C¹ and vanishing with its gradient on B_Δ(0), give error 9/Δ at x = Δ (resp. x = 0); the proof (p.19) uses the gradient bound only on these segments (Lipschitz constant on the convex hull K)
--   - correction: case (ii): {f̃_{2,Δ}} provides order-N^f_2 function accuracy of f₂ near f₁(x₀), i.e. on B_Δ(f₁(x₀)) → 0 ≤ N^f_2, 0 ≤ κ^f_2 and |f₂(f₁(x)) − f̃_{2,Δ}(f₁(x))| ≤ κ^f_2 Δ^{N^f_2} for all x ∈ B_Δ(x₀); reason: f₁(x) leaves B_Δ(f₁(x₀)) when M̄_{∇f₁}(x₀) > 1 (the case-(ii) examples above); the proof (p.19) applies the accuracy at f₁(x); when M̄ ≤ 1 the printed hypothesis implies this one by Lemma 29; case (i) keeps the printed hypothesis at f₁(x₀)
--   - correction: K^f_F(x₀) = M_{∇f̃₂}(f₁(x₀)) κ^f_1 Δ̄^{N^f_1 − N^f_F} + M̄_{∇f₁}(x₀)^{N^f_2} κ^f_2 Δ̄^{N^f_2 − N^f_F} → K = M_{∇f̃₂} κ^f_1 Δ̄^{N^f_1 − N^f_F} + κ^f_2 Δ̄^{N^f_2 − N^f_F}; reason: false as printed: f₁ = f̃₁ = 0, f₂ = 0, f̃_{2,Δ} ≡ Δ, N^f_1 = N^f_2 = 1, κ^f_1 = 0, κ^f_2 = 1 give M̄ = 0, printed K = 0, error Δ; the factor M̄^{N^f_2} only appears if the accuracy constant is rescaled, which the hypotheses do not give
-- source:
--   Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Theorem 30 and its proof, p.19; Lemma 29, p.18; standing assumptions of §5, p.18

import Mathlib
import Definitions.Def_SurrogateOps_FunAccAt
import Definitions.Def_SurrogateOps_FunAccNear
import Definitions.Def_SurrogateOps_Supplement_VecFunAccAt
import Definitions.Def_SurrogateOps_Supplement_VecFunAccNear

namespace SurrogateOps.Supplement

/-- **Theorem 30 (Function accuracy at/near `x0`), corrected.** Chen, Hare, Jarry-Bolduc, Error
Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1,
Theorem 30 and its proof, p.19 (standing assumptions of §5, p.18).
For `f₁ : ℝ^d → ℝ^m` in `C¹`, `f₂ : ℝ^m → ℝ`, `F = f₂ ∘ f₁`, `F̃_Δ = f̃_{2,Δ} ∘ f̃_{1,Δ}`,
`N^f_F = min{N^f_1, N^f_2}`, `N^f_1 > 0` and `{f̃_{2,Δ}} ⊆ C¹`:
(i) if `{f̃_{1,Δ}}` provides order-`N^f_1` function accuracy of `f₁` at `x0` with constant `κ^f_1`,
`{f̃_{2,Δ}}` provides order-`N^f_2` function accuracy of `f₂` at `f₁(x0)` with constant `κ^f_2`, and
`‖∇f̃_{2,Δ}‖ ≤ M_{∇f̃₂}` on the segment `[f₁(x0), f̃_{1,Δ}(x0)]`, then
`|F(x0) - F̃_Δ(x0)| ≤ K Δ^{N^f_F}`;
(ii) if `{f̃_{1,Δ}}` provides order-`N^f_1` function accuracy of `f₁` near `x0`,
`|f₂(f₁(x)) - f̃_{2,Δ}(f₁(x))| ≤ κ^f_2 Δ^{N^f_2}` and `‖∇f̃_{2,Δ}‖ ≤ M_{∇f̃₂}` on `[f₁(x), f̃_{1,Δ}(x)]`
for all `x ∈ B_Δ(x0)`, then `|F(x) - F̃_Δ(x)| ≤ K Δ^{N^f_F}` for all `x ∈ B_Δ(x0)`;
with `K = M_{∇f̃₂} κ^f_1 Δ̄^{N^f_1 - N^f_F} + κ^f_2 Δ̄^{N^f_2 - N^f_F}`; and `{F̃_Δ}` provides
order-`N^f_F` function accuracy of `F` at/near `x0`.

**Formalization Note.** As printed the theorem is false (counterexamples in `DISPROOF.md`): the
hypotheses on `f̃_{2,Δ}` are stated at/near `f₁(x0)`, while the proof uses them at the points
`f₁(x)` and on the segments `[f₁(x), f̃_{1,Δ}(x)]`, and the factor `M̄_{∇f₁}(x0)^{N^f_2}` in `K` cannot be
kept. This statement uses exactly what the proof uses. In case (i) the accuracy hypothesis on `f₂` is
the printed one. `Mt₂` is the bound `M_{∇f̃₂}`, a hypothesis rather than an `sSup`. -/
theorem theorem_30 {d m : ℕ} (f₁ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m))
    (f₂ : EuclideanSpace ℝ (Fin m) → ℝ)
    (fm₁ : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m))
    (fm₂ : ℝ → EuclideanSpace ℝ (Fin m) → ℝ) (x0 : EuclideanSpace ℝ (Fin d))
    (Δbar N₁ N₂ κ₁ κ₂ Mt₂ NF K : ℝ)
    (hΔbar : 0 < Δbar) (hf₁ : ContDiff ℝ 1 f₁)
    (hm₂ : ∀ Δ ∈ Set.Ioc 0 Δbar, ContDiff ℝ 1 (fm₂ Δ))
    (hN₁ : 0 < N₁) (hNF : NF = min N₁ N₂)
    (hK : K = Mt₂ * κ₁ * Δbar ^ (N₁ - NF) + κ₂ * Δbar ^ (N₂ - NF)) :
    (VecFunAccAt f₁ fm₁ x0 Δbar N₁ κ₁ → FunAccAt f₂ fm₂ (f₁ x0) Δbar N₂ κ₂ →
      (∀ Δ ∈ Set.Ioc 0 Δbar, ∀ y ∈ segment ℝ (f₁ x0) (fm₁ Δ x0), ‖fderiv ℝ (fm₂ Δ) y‖ ≤ Mt₂) →
      (∀ Δ ∈ Set.Ioc 0 Δbar, |f₂ (f₁ x0) - fm₂ Δ (fm₁ Δ x0)| ≤ K * Δ ^ NF) ∧
      ∃ κ, FunAccAt (fun x => f₂ (f₁ x)) (fun Δ x => fm₂ Δ (fm₁ Δ x)) x0 Δbar NF κ) ∧
    (VecFunAccNear f₁ fm₁ x0 Δbar N₁ κ₁ → 0 ≤ N₂ → 0 ≤ κ₂ →
      (∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ,
        |f₂ (f₁ x) - fm₂ Δ (f₁ x)| ≤ κ₂ * Δ ^ N₂) →
      (∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ,
        ∀ y ∈ segment ℝ (f₁ x) (fm₁ Δ x), ‖fderiv ℝ (fm₂ Δ) y‖ ≤ Mt₂) →
      (∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ,
        |f₂ (f₁ x) - fm₂ Δ (fm₁ Δ x)| ≤ K * Δ ^ NF) ∧
      ∃ κ, FunAccNear (fun x => f₂ (f₁ x)) (fun Δ x => fm₂ Δ (fm₁ Δ x)) x0 Δbar NF κ) := by sorry

end SurrogateOps.Supplement
