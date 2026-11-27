-- Prove2me | Theorems.Thm_SurrogateOps_Supplement_theorem_32
-- name    : SurrogateOps.Supplement.theorem_32
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:43:57.114798+00:00
-- url     : https://prove2.me/theorems/3667c556-1bfa-4fb2-bba9-5eeab41011e3
-- title:
--   Theorem 32, pp.20–21 (corrected: accuracy and $\nabla^2$-bound of $\tilde f_{2,\Delta}$ at the points the proof uses) — gradient accuracy of a composition near $x_0$ of order $\min\{N^f_i,N^g_i\}$
-- statement:
--   Let $f_1:\mathbb R^d\to\mathbb R^m$ and $f_2:\mathbb R^m\to\mathbb R$ be $C^1$, $F=f_2\circ f_1$ and $\tilde F_\Delta=\tilde f_{2,\Delta}\circ\tilde f_{1,\Delta}$. Suppose:
--
--   1. $\{\tilde f_{1,\Delta}\}_{(0,\bar\Delta]}$ provides order-$N^f_1$ function accuracy and order-$N^g_1$ gradient accuracy of $f_1$ near $x_0$, and $N^f_1>0$;
--   2. for all $\Delta\in(0,\bar\Delta]$ and $x\in B_\Delta(x_0)$, $|f_2(f_1(x))-\tilde f_{2,\Delta}(f_1(x))|\le\kappa^f_2\Delta^{N^f_2}$ and $\|\nabla f_2(f_1(x))-\nabla\tilde f_{2,\Delta}(f_1(x))\|\le\kappa^g_2\Delta^{N^g_2}$ (orders and constants nonnegative);
--   3. every $\tilde f_{2,\Delta}$ is $C^2$ and $\|\nabla^2\tilde f_{2,\Delta}(y)\|\le M_{\nabla^2\tilde f_2}$ for all $y$ on the segments $[f_1(x),\tilde f_{1,\Delta}(x)]$, $x\in B_\Delta(x_0)$.
--
--   Then $\{\tilde F_\Delta\}_{(0,\bar\Delta]}$ provides order-$N^{fg}_F$ gradient accuracy of $F$ near $x_0$, where $N^{fg}_F=\min\{N^f_1,N^f_2,N^g_1,N^g_2\}$.
--
--   The printed theorem assumes the accuracy and the Hessian bound of the outer models near $f_1(x_0)$, i.e. on $B_\Delta(f_1(x_0))$; it is false, because the points $f_1(x)$ and $\tilde f_{1,\Delta}(x)$ used by the proof (p.21) leave that ball. Items 2 and 3 are exactly what the two displays of the proof use.
--
--   **Formalization Note** Accuracy of $f_1$ uses the vector-valued predicates; $\nabla f_1$ is the Jacobian with its operator norm. The inner models are assumed differentiable on $B_\Delta(x_0)$.
--
--   Differences from the source:
--   - encoding: f₁ : ℝ^d → ℝ^m, f₂ : ℝ^m → ℝ, the closed balls, classes of models of f₁ and f₂ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m), EuclideanSpace ℝ (Fin m) → ℝ, Metric.closedBall, maps ℝ → E → G used only on Set.Ioc 0 Δbar; accuracy of f₁ by the vector-valued predicates SurrogateOps.Supplement.Vec*; reason: Lean convention; the vector-valued predicates are Definition 1 with the norm of ℝ^m; same instances
--   - encoding: the gradient ∇f and its Euclidean norm → fderiv ℝ f with the operator norm of E →L[ℝ] ℝ; reason: on EuclideanSpace the two norms agree by Riesz representation; same instances
--   - encoding: the Hessian ∇²f as a matrix → fderiv ℝ (fderiv ℝ f) as a bilinear map; reason: the matrix and the second derivative determine each other; same instances
--   - reading: ‖·‖ on Hessians is unspecified → the operator norm of E →L[ℝ] E →L[ℝ] ℝ; reason: the spectral norm is the standard matrix norm in this literature and the one the proof's ‖ab^⊤‖ = ‖a‖‖b‖ uses; on a matrix it equals the operator norm of the bilinear map
--   - reading: ‖∇f₁‖ and ‖∇²f₁‖ for the vector-valued map f₁ are unspecified → the operator norms of the Jacobian fderiv ℝ f₁ x : ℝ^d →L[ℝ] ℝ^m and of fderiv ℝ (fderiv ℝ f₁) x : ℝ^d →L[ℝ] ℝ^d →L[ℝ] ℝ^m; reason: the proof's estimates ‖∇f₁^⊤ v‖ ≤ ‖∇f₁‖‖v‖ hold for the operator norm; a componentwise norm would change the constants
--   - encoding: provides order-N accuracy: ∃ κ ≥ 0 → the constant κ is an explicit argument of the predicate, with 0 ≤ N and 0 ≤ κ as clauses; the order clause of the conclusion is ∃ κ; reason: a universally quantified κ in a hypothesis is the same as an existential one; the conclusion's κ depends on neither Δ nor x
--   - encoding: min{…} of finitely many orders → nested binary min of the reals; reason: same value
--   - reading: ∇f̃_{1,Δ}(x) is used without stating the regularity of the models → DifferentiableAt ℝ (fm₁ Δ) x for every Δ ∈ (0, Δ̄] and every x ∈ B_Δ(x₀); reason: the page's ∇f̃_{1,Δ}(x) presupposes it; Lean's fderiv is 0 at a non-differentiable point, where the product, quotient and chain rules fail
--   - encoding: {f̃_{2,Δ}}_{(0,Δ̄]} ⊆ C² → ContDiff ℝ 2 (fm₂ Δ) for every Δ ∈ (0, Δ̄]; reason: same instances
--   - correction: {f̃_{2,Δ}} provides function and gradient accuracy of f₂ near f₁(x₀), i.e. on B_Δ(f₁(x₀)) → the same function and gradient accuracy bounds of f̃_{2,Δ} at the points f₁(x), x ∈ B_Δ(x₀), with nonnegative orders and constants; reason: false as printed: d = m = 1, x₀ = 0, f₂ = 0, f̃_{2,Δ}(y) = max(0, y² − Δ²)³/Δ⁸ (C², vanishing with its first two derivatives on B_Δ(0)); with f₁ = f̃₁ = 2x the gradient error at x = Δ is 216/Δ³, with f₁ = 0, f̃_{1,Δ}(x) = x + 2Δ it is 108/Δ³ at x = 0; the displays of the proof apply the accuracy at f₁(x), which leaves B_Δ(f₁(x₀))
--   - correction: {‖∇²f̃_{2,Δ}‖}_{(0,Δ̄]} is uniformly bounded near f₁(x₀) by M_{∇²f̃₂}(f₁(x₀)) → ‖∇²f̃_{2,Δ}(y)‖ ≤ M_{∇²f̃₂} for y on the segments [f₁(x), f̃_{1,Δ}(x)], x ∈ B_Δ(x₀); reason: the same counterexample: ∇²f̃_{2,Δ} vanishes on B_Δ(0) but not on the segments; the proof's second display (p.21) is a mean-value bound along these segments
-- source:
--   Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Theorem 32, p.20, and its proof, p.21; standing assumptions of §5, p.18

import Mathlib
import Definitions.Def_SurrogateOps_GradAccNear
import Definitions.Def_SurrogateOps_Supplement_VecFunAccNear
import Definitions.Def_SurrogateOps_Supplement_VecGradAccNear

namespace SurrogateOps.Supplement

/-- **Theorem 32 (Gradient accuracy near `x0`), corrected.** Chen, Hare, Jarry-Bolduc, Error
Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1,
Theorem 32, p.20, and its proof, p.21 (standing assumptions of §5, p.18).
For `f₁ : ℝ^d → ℝ^m`, `f₂ : ℝ^m → ℝ` in `C¹`, `F = f₂ ∘ f₁`, `F̃_Δ = f̃_{2,Δ} ∘ f̃_{1,Δ}`: if
`{f̃_{1,Δ}}` provides order-`N^f_1` function and order-`N^g_1` gradient accuracy of `f₁` near `x0`,
`f̃_{2,Δ}` has order-`N^f_2` function and order-`N^g_2` gradient accuracy of `f₂` at the points
`f₁(x)`, `x ∈ B_Δ(x0)`, `N^f_1 > 0`, `{f̃_{2,Δ}} ⊆ C²`, and `‖∇²f̃_{2,Δ}‖ ≤ M_{∇²f̃₂}` on the segments
`[f₁(x), f̃_{1,Δ}(x)]`, `x ∈ B_Δ(x0)`, then `{F̃_Δ}` provides order-`N^{fg}_F` gradient accuracy of `F`
near `x0`, `N^{fg}_F = min{N^f_1, N^f_2, N^g_1, N^g_2}`.

**Formalization Note.** As printed the theorem is false (counterexamples in `DISPROOF.md`): the page
assumes accuracy and the Hessian bound of `f̃_{2,Δ}` near `f₁(x0)` (on `B_Δ(f₁(x0))`), while the two
displays of the proof use them at `f₁(x)` and on `[f₁(x), f̃_{1,Δ}(x)]`, which leave that ball. This
statement assumes exactly what the proof uses. `∇f₁` is the Jacobian with its operator norm, `∇²f̃₂` is
`fderiv ℝ (fderiv ℝ ·)` with its operator norm. `hm₁` states that `∇f̃_{1,Δ}` exists on `B_Δ(x0)`. -/
theorem theorem_32 {d m : ℕ} (f₁ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m))
    (f₂ : EuclideanSpace ℝ (Fin m) → ℝ)
    (fm₁ : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m))
    (fm₂ : ℝ → EuclideanSpace ℝ (Fin m) → ℝ) (x0 : EuclideanSpace ℝ (Fin d))
    (Δbar Nf₁ Nf₂ Ng₁ Ng₂ κf₁ κf₂ κg₁ κg₂ Mht₂ NF : ℝ)
    (hΔbar : 0 < Δbar) (hf₁ : ContDiff ℝ 1 f₁) (hf₂ : ContDiff ℝ 1 f₂)
    (hm₁ : ∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ, DifferentiableAt ℝ (fm₁ Δ) x)
    (hm₂ : ∀ Δ ∈ Set.Ioc 0 Δbar, ContDiff ℝ 2 (fm₂ Δ))
    (hfa₁ : VecFunAccNear f₁ fm₁ x0 Δbar Nf₁ κf₁)
    (hg₁ : VecGradAccNear f₁ fm₁ x0 Δbar Ng₁ κg₁)
    (hNf₂ : 0 ≤ Nf₂) (hκf₂ : 0 ≤ κf₂) (hNg₂ : 0 ≤ Ng₂) (hκg₂ : 0 ≤ κg₂)
    (hfa₂ : ∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ,
      |f₂ (f₁ x) - fm₂ Δ (f₁ x)| ≤ κf₂ * Δ ^ Nf₂)
    (hg₂ : ∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ,
      ‖fderiv ℝ f₂ (f₁ x) - fderiv ℝ (fm₂ Δ) (f₁ x)‖ ≤ κg₂ * Δ ^ Ng₂)
    (hN₁ : 0 < Nf₁)
    (hMht₂ : ∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ,
      ∀ y ∈ segment ℝ (f₁ x) (fm₁ Δ x), ‖fderiv ℝ (fderiv ℝ (fm₂ Δ)) y‖ ≤ Mht₂)
    (hNF : NF = min (min Nf₁ Nf₂) (min Ng₁ Ng₂)) :
    ∃ κ, GradAccNear (fun x => f₂ (f₁ x)) (fun Δ x => fm₂ Δ (fm₁ Δ x)) x0 Δbar NF κ := by sorry

end SurrogateOps.Supplement
