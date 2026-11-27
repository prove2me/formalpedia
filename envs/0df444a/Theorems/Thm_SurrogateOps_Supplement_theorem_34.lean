-- Prove2me | Theorems.Thm_SurrogateOps_Supplement_theorem_34
-- name    : SurrogateOps.Supplement.theorem_34
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:44:45.979285+00:00
-- url     : https://prove2.me/theorems/9f1cfb7f-a186-47ce-ac0a-50c8554ee8ab
-- title:
--   Theorem 34, p.22 (corrected: accuracy and $\nabla^3$-bound of $\tilde f_{2,\Delta}$ at the points the proof uses) — Hessian accuracy of a composition near $x_0$ of order $\min\{N^f_i,N^g_i,N^h_i\}$
-- statement:
--   Let $f_1:\mathbb R^d\to\mathbb R^m$ and $f_2:\mathbb R^m\to\mathbb R$ be $C^2$, $F=f_2\circ f_1$ and $\tilde F_\Delta=\tilde f_{2,\Delta}\circ\tilde f_{1,\Delta}$. Suppose:
--
--   1. $\{\tilde f_{1,\Delta}\}_{(0,\bar\Delta]}$ provides order-$N^f_1$ function, order-$N^g_1$ gradient and order-$N^h_1$ Hessian accuracy of $f_1$ near $x_0$, and $N^f_1>0$;
--   2. for all $\Delta\in(0,\bar\Delta]$ and $x\in B_\Delta(x_0)$, the function, gradient and Hessian errors of $\tilde f_{2,\Delta}$ at $f_1(x)$ are at most $\kappa^f_2\Delta^{N^f_2}$, $\kappa^g_2\Delta^{N^g_2}$, $\kappa^h_2\Delta^{N^h_2}$ (orders and constants nonnegative);
--   3. every $\tilde f_{2,\Delta}$ is $C^3$ and $\|\nabla^3\tilde f_{2,\Delta}(y)\|\le M_{\nabla^3\tilde f_2}$ for all $y$ on the segments $[f_1(x),\tilde f_{1,\Delta}(x)]$, $x\in B_\Delta(x_0)$.
--
--   Then $\{\tilde F_\Delta\}_{(0,\bar\Delta]}$ provides order-$N^{fgh}_F$ Hessian accuracy of $F$ near $x_0$, where $N^{fgh}_F=\min\{N^f_1,N^f_2,N^g_1,N^g_2,N^h_1,N^h_2\}$.
--
--   As for Theorem 32, the printed hypotheses near $f_1(x_0)$ do not reach the points the proof uses, and the printed theorem is false; items 2 and 3 are exactly what the four displays of the proof (p.22) use.
--
--   **Formalization Note** $\nabla^3\tilde f_{2,\Delta}$ is `iteratedFDeriv ℝ 3`, the third derivative as a trilinear form, with its operator norm. The inner models are assumed twice differentiable around every point of $B_\Delta(x_0)$.
--
--   Differences from the source:
--   - encoding: f₁ : ℝ^d → ℝ^m, f₂ : ℝ^m → ℝ, the closed balls, classes of models of f₁ and f₂ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m), EuclideanSpace ℝ (Fin m) → ℝ, Metric.closedBall, maps ℝ → E → G used only on Set.Ioc 0 Δbar; accuracy of f₁ by the vector-valued predicates SurrogateOps.Supplement.Vec*; reason: Lean convention; the vector-valued predicates are Definition 1 with the norm of ℝ^m; same instances
--   - encoding: the gradient ∇f and its Euclidean norm → fderiv ℝ f with the operator norm of E →L[ℝ] ℝ; reason: on EuclideanSpace the two norms agree by Riesz representation; same instances
--   - encoding: the Hessian ∇²f as a matrix → fderiv ℝ (fderiv ℝ f) as a bilinear map; reason: the matrix and the second derivative determine each other; same instances
--   - reading: ‖·‖ on Hessians is unspecified → the operator norm of E →L[ℝ] E →L[ℝ] ℝ; reason: the spectral norm is the standard matrix norm in this literature and the one the proof's ‖ab^⊤‖ = ‖a‖‖b‖ uses; on a matrix it equals the operator norm of the bilinear map
--   - reading: ‖∇f₁‖ and ‖∇²f₁‖ for the vector-valued map f₁ are unspecified → the operator norms of the Jacobian fderiv ℝ f₁ x : ℝ^d →L[ℝ] ℝ^m and of fderiv ℝ (fderiv ℝ f₁) x : ℝ^d →L[ℝ] ℝ^d →L[ℝ] ℝ^m; reason: the proof's estimates ‖∇f₁^⊤ v‖ ≤ ‖∇f₁‖‖v‖ hold for the operator norm; a componentwise norm would change the constants
--   - encoding: provides order-N accuracy: ∃ κ ≥ 0 → the constant κ is an explicit argument of the predicate, with 0 ≤ N and 0 ≤ κ as clauses; the order clause of the conclusion is ∃ κ; reason: a universally quantified κ in a hypothesis is the same as an existential one; the conclusion's κ depends on neither Δ nor x
--   - encoding: min{…} of finitely many orders → nested binary min of the reals; reason: same value
--   - reading: ∇²f̃_{1,Δ}(x) is used without stating the regularity of the models → ContDiffAt ℝ 2 (fm₁ Δ) x for every Δ ∈ (0, Δ̄] and every x ∈ B_Δ(x₀); reason: the page's ∇²f̃_{1,Δ}(x) presupposes it; Lean's fderiv is 0 at a non-differentiable point, where the product, quotient and chain rules fail
--   - encoding: {f̃_{2,Δ}}_{(0,Δ̄]} ⊆ C³ and ∇³f̃_{2,Δ} → ContDiff ℝ 3 (fm₂ Δ) for every Δ ∈ (0, Δ̄], and iteratedFDeriv ℝ 3 (fm₂ Δ) with its operator norm; reason: the third derivative as a trilinear form; same instances
--   - correction: {f̃_{2,Δ}} provides function, gradient and Hessian accuracy of f₂ near f₁(x₀), i.e. on B_Δ(f₁(x₀)) → the same function, gradient and Hessian accuracy bounds of f̃_{2,Δ} at the points f₁(x), x ∈ B_Δ(x₀), with nonnegative orders and constants; reason: false as printed: d = m = 1, x₀ = 0, f₂ = 0, f̃_{2,Δ}(y) = max(0, y² − Δ²)⁴/Δ¹¹ (C³, vanishing with its first three derivatives on B_Δ(0)); with f₁ = f̃₁ = 2x the Hessian error at x = Δ is 7776/Δ⁵, with f₁ = 0, f̃_{1,Δ}(x) = x + 2Δ it is 1944/Δ⁵ at x = 0; the displays of the proof apply the accuracy at f₁(x), which leaves B_Δ(f₁(x₀))
--   - correction: {‖∇³f̃_{2,Δ}‖}_{(0,Δ̄]} is uniformly bounded near f₁(x₀) by M_{∇³f̃₂}(f₁(x₀)) → ‖∇³f̃_{2,Δ}(y)‖ ≤ M_{∇³f̃₂} for y on the segments [f₁(x), f̃_{1,Δ}(x)], x ∈ B_Δ(x₀); reason: the same counterexample: the derivatives of f̃_{2,Δ} vanish on B_Δ(0) but not on the segments; the proof's last display (p.22) is a mean-value bound along these segments
-- source:
--   Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Theorem 34 and its proof, p.22; standing assumptions of §5, p.18

import Mathlib
import Definitions.Def_SurrogateOps_HessAccNear
import Definitions.Def_SurrogateOps_Supplement_VecFunAccNear
import Definitions.Def_SurrogateOps_Supplement_VecGradAccNear
import Definitions.Def_SurrogateOps_Supplement_VecHessAccNear

namespace SurrogateOps.Supplement

/-- **Theorem 34 (Hessian accuracy near `x0`), corrected.** Chen, Hare, Jarry-Bolduc, Error
Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1,
Theorem 34 and its proof, p.22 (standing assumptions of §5, p.18).
For `f₁ : ℝ^d → ℝ^m`, `f₂ : ℝ^m → ℝ` in `C²`, `F = f₂ ∘ f₁`, `F̃_Δ = f̃_{2,Δ} ∘ f̃_{1,Δ}`: if
`{f̃_{1,Δ}}` provides order-`N^f_1` function, order-`N^g_1` gradient and order-`N^h_1` Hessian accuracy
of `f₁` near `x0`, `f̃_{2,Δ}` has order-`N^f_2` function, order-`N^g_2` gradient and order-`N^h_2`
Hessian accuracy of `f₂` at the points `f₁(x)`, `x ∈ B_Δ(x0)`, `N^f_1 > 0`, `{f̃_{2,Δ}} ⊆ C³`, and
`‖∇³f̃_{2,Δ}‖ ≤ M_{∇³f̃₂}` on the segments `[f₁(x), f̃_{1,Δ}(x)]`, `x ∈ B_Δ(x0)`, then `{F̃_Δ}` provides
order-`N^{fgh}_F` Hessian accuracy of `F` near `x0`,
`N^{fgh}_F = min{N^f_1, N^f_2, N^g_1, N^g_2, N^h_1, N^h_2}`.

**Formalization Note.** As printed the theorem is false (counterexamples in `DISPROOF.md`): the page
assumes accuracy and the third-derivative bound of `f̃_{2,Δ}` near `f₁(x0)`, while the four displays of
the proof use them at `f₁(x)` and on `[f₁(x), f̃_{1,Δ}(x)]`. This statement assumes exactly what the
proof uses. `∇³f̃₂` is `iteratedFDeriv ℝ 3`, the third derivative as a trilinear map, with its operator
norm; Jacobian and second derivative of `f₁` are as in Theorem 33. `hm₁` states that
`∇²f̃_{1,Δ}` exists on `B_Δ(x0)` (`ContDiffAt`: every `C²` model qualifies). -/
theorem theorem_34 {d m : ℕ} (f₁ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m))
    (f₂ : EuclideanSpace ℝ (Fin m) → ℝ)
    (fm₁ : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m))
    (fm₂ : ℝ → EuclideanSpace ℝ (Fin m) → ℝ) (x0 : EuclideanSpace ℝ (Fin d))
    (Δbar Nf₁ Nf₂ Ng₁ Ng₂ Nh₁ Nh₂ κf₁ κf₂ κg₁ κg₂ κh₁ κh₂ M3t₂ NF : ℝ)
    (hΔbar : 0 < Δbar) (hf₁ : ContDiff ℝ 2 f₁) (hf₂ : ContDiff ℝ 2 f₂)
    (hm₁ : ∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ, ContDiffAt ℝ 2 (fm₁ Δ) x)
    (hm₂ : ∀ Δ ∈ Set.Ioc 0 Δbar, ContDiff ℝ 3 (fm₂ Δ))
    (hfa₁ : VecFunAccNear f₁ fm₁ x0 Δbar Nf₁ κf₁)
    (hg₁ : VecGradAccNear f₁ fm₁ x0 Δbar Ng₁ κg₁)
    (hh₁ : VecHessAccNear f₁ fm₁ x0 Δbar Nh₁ κh₁)
    (hNf₂ : 0 ≤ Nf₂) (hκf₂ : 0 ≤ κf₂) (hNg₂ : 0 ≤ Ng₂) (hκg₂ : 0 ≤ κg₂)
    (hNh₂ : 0 ≤ Nh₂) (hκh₂ : 0 ≤ κh₂)
    (hfa₂ : ∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ,
      |f₂ (f₁ x) - fm₂ Δ (f₁ x)| ≤ κf₂ * Δ ^ Nf₂)
    (hg₂ : ∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ,
      ‖fderiv ℝ f₂ (f₁ x) - fderiv ℝ (fm₂ Δ) (f₁ x)‖ ≤ κg₂ * Δ ^ Ng₂)
    (hh₂ : ∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ,
      ‖fderiv ℝ (fderiv ℝ f₂) (f₁ x) - fderiv ℝ (fderiv ℝ (fm₂ Δ)) (f₁ x)‖ ≤ κh₂ * Δ ^ Nh₂)
    (hN₁ : 0 < Nf₁)
    (hM3t₂ : ∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ,
      ∀ y ∈ segment ℝ (f₁ x) (fm₁ Δ x), ‖iteratedFDeriv ℝ 3 (fm₂ Δ) y‖ ≤ M3t₂)
    (hNF : NF = min (min (min Nf₁ Nf₂) (min Ng₁ Ng₂)) (min Nh₁ Nh₂)) :
    ∃ κ, HessAccNear (fun x => f₂ (f₁ x)) (fun Δ x => fm₂ Δ (fm₁ Δ x)) x0 Δbar NF κ := by sorry

end SurrogateOps.Supplement
