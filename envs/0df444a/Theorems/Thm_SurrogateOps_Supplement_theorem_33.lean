-- Prove2me | Theorems.Thm_SurrogateOps_Supplement_theorem_33
-- name    : SurrogateOps.Supplement.theorem_33
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:44:22.486905+00:00
-- url     : https://prove2.me/theorems/b37c69fa-bb34-56dd-b515-a9cb46cf6a04
-- title:
--   Theorem 33, pp.21–22 — Hessian accuracy at $x_0$ of a composition of models exact at $x_0$ and $f_1(x_0)$, with the explicit constant $K^h_F(x_0)$
-- statement:
--   Let $f_1:\mathbb R^d\to\mathbb R^m$ and $f_2:\mathbb R^m\to\mathbb R$ be $C^2$, $F=f_2\circ f_1$ and $\tilde F_\Delta=\tilde f_{2,\Delta}\circ\tilde f_{1,\Delta}$. Suppose $\tilde f_{1,\Delta}(x_0)=f_1(x_0)$ and $\{\tilde f_{1,\Delta}\}$ provides order-$N^g_1$ gradient and order-$N^h_1$ Hessian accuracy of $f_1$ at $x_0$ with constants $\kappa^g_1(x_0)$, $\kappa^h_1(x_0)$; and $\tilde f_{2,\Delta}(f_1(x_0))=f_2(f_1(x_0))$ and $\{\tilde f_{2,\Delta}\}$ provides order-$N^g_2$ gradient and order-$N^h_2$ Hessian accuracy of $f_2$ at $f_1(x_0)$ with constants $\kappa^g_2$, $\kappa^h_2$. Let $M_{\nabla\tilde f_1}(x_0)$, $M_{\nabla^2\tilde f_1}(x_0)$ bound $\|\nabla\tilde f_{1,\Delta}(x_0)\|$, $\|\nabla^2\tilde f_{1,\Delta}(x_0)\|$ and $M_{\nabla\tilde f_2}$, $M_{\nabla^2\tilde f_2}$ bound $\|\nabla\tilde f_{2,\Delta}(f_1(x_0))\|$, $\|\nabla^2\tilde f_{2,\Delta}(f_1(x_0))\|$ uniformly in $\Delta$, and $N^{gh}_F=\min\{N^g_1,N^g_2,N^h_1,N^h_2\}$. Then for every $\Delta\in(0,\bar\Delta]$, $\|\nabla^2F(x_0)-\nabla^2\tilde F_\Delta(x_0)\|\le K^h_F(x_0)\Delta^{N^{gh}_F}$ with
--
--   $$
--   \begin{aligned}
--   K^h_F(x_0)={}&M_{\nabla^2\tilde f_2}\bigl(\|\nabla f_1(x_0)\|+M_{\nabla\tilde f_1}\bigr)\kappa^g_1\bar\Delta^{N^g_1-N^{gh}_F}+M_{\nabla^2\tilde f_1}\kappa^g_2\bar\Delta^{N^g_2-N^{gh}_F}\\
--   &+\bigl(\|\nabla f_2(f_1(x_0))\|+M_{\nabla\tilde f_2}\bigr)\kappa^h_1\bar\Delta^{N^h_1-N^{gh}_F}+\|\nabla f_1(x_0)\|^2\kappa^h_2\bar\Delta^{N^h_2-N^{gh}_F}.
--   \end{aligned}
--   $$
--
--   In particular $\{\tilde F_\Delta\}_{(0,\bar\Delta]}$ provides order-$N^{gh}_F$ Hessian accuracy of $F$ at $x_0$.
--
--   **Formalization Note** $\nabla f_1$ is the Jacobian and $\nabla^2f_1$ the second derivative as a bilinear map into $\mathbb R^m$, each with its operator norm. The models are assumed twice differentiable around $x_0$ and $f_1(x_0)$ respectively.
--
--   Differences from the source:
--   - encoding: f₁ : ℝ^d → ℝ^m, f₂ : ℝ^m → ℝ, the closed balls, classes of models of f₁ and f₂ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m), EuclideanSpace ℝ (Fin m) → ℝ, Metric.closedBall, maps ℝ → E → G used only on Set.Ioc 0 Δbar; accuracy of f₁ by the vector-valued predicates SurrogateOps.Supplement.Vec*; reason: Lean convention; the vector-valued predicates are Definition 1 with the norm of ℝ^m; same instances
--   - encoding: the gradient ∇f and its Euclidean norm → fderiv ℝ f with the operator norm of E →L[ℝ] ℝ; reason: on EuclideanSpace the two norms agree by Riesz representation; same instances
--   - encoding: the Hessian ∇²f as a matrix → fderiv ℝ (fderiv ℝ f) as a bilinear map; reason: the matrix and the second derivative determine each other; same instances
--   - reading: ‖·‖ on Hessians is unspecified → the operator norm of E →L[ℝ] E →L[ℝ] ℝ; reason: the spectral norm is the standard matrix norm in this literature and the one the proof's ‖ab^⊤‖ = ‖a‖‖b‖ uses; on a matrix it equals the operator norm of the bilinear map
--   - reading: ‖∇f₁‖ and ‖∇²f₁‖ for the vector-valued map f₁ are unspecified → the operator norms of the Jacobian fderiv ℝ f₁ x : ℝ^d →L[ℝ] ℝ^m and of fderiv ℝ (fderiv ℝ f₁) x : ℝ^d →L[ℝ] ℝ^d →L[ℝ] ℝ^m; reason: the proof's estimates ‖∇f₁^⊤ v‖ ≤ ‖∇f₁‖‖v‖ hold for the operator norm; a componentwise norm would change the constants
--   - encoding: provides order-N accuracy: ∃ κ ≥ 0 → the constant κ is an explicit argument of the predicate, with 0 ≤ N and 0 ≤ κ as clauses; the order clause of the conclusion is ∃ κ; reason: a universally quantified κ in a hypothesis is the same as an existential one; the conclusion's κ depends on neither Δ nor x
--   - encoding: order-∞ function accuracy at a point with constant 0 → equality of model and function at that point for every Δ ∈ (0, Δ̄]; reason: the page states the equivalence itself (p.6)
--   - reading: ∇²f̃_{1,Δ}(x₀), ∇²f̃_{2,Δ}(f₁(x₀)) is used without stating the regularity of the models → ContDiffAt ℝ 2 (fm₁ Δ) x0 and ContDiffAt ℝ 2 (fm₂ Δ) (f₁ x0) for every Δ ∈ (0, Δ̄] at x₀ and at f₁(x₀); reason: the page's ∇²f̃_{1,Δ}(x₀), ∇²f̃_{2,Δ}(f₁(x₀)) presupposes it; Lean's fderiv is 0 at a non-differentiable point, where the product, quotient and chain rules fail
--   - encoding: min{…} of finitely many orders → nested binary min of the reals; reason: same value
--   - encoding: the constant K(x₀) → a variable fixed by an equation hypothesis (or written out in the conclusion); reason: same as the page's "Let" and "where"
--   - encoding: M-bounds M_{∇f̃₁}(x₀), M_{∇²f̃₁}(x₀), M_{∇f̃₂}(f₁(x₀)), M_{∇²f̃₂}(f₁(x₀)) → numbers with bounding hypotheses on the model derivatives at x₀ and at f₁(x₀) for Δ ∈ (0, Δ̄]; reason: the page says "we use … to denote these bounds" (p.4); the theorem holds for every valid choice, and no sSup junk value can enter
-- source:
--   Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Theorem 33, p.21, and its proof, pp.21–22; standing assumptions of §5, p.18

import Mathlib
import Definitions.Def_SurrogateOps_GradAccAt
import Definitions.Def_SurrogateOps_HessAccAt
import Definitions.Def_SurrogateOps_Supplement_VecGradAccAt
import Definitions.Def_SurrogateOps_Supplement_VecHessAccAt

namespace SurrogateOps.Supplement

/-- **Theorem 33 (Hessian accuracy at `x0`).** Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate
Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Theorem 33, p.21 (standing
assumptions of §5, p.18).
For `f₁ : ℝ^d → ℝ^m`, `f₂ : ℝ^m → ℝ` in `C²`, `F = f₂ ∘ f₁`, `F̃_Δ = f̃_{2,Δ} ∘ f̃_{1,Δ}`, models exact
at `x0` and at `f₁(x0)` respectively, and `N^{gh}_F = min{N^g_1, N^g_2, N^h_1, N^h_2}`:
`‖∇²F(x0) - ∇²F̃_Δ(x0)‖ ≤ K Δ^{N^{gh}_F}` with `K` the constant of the page, and `{F̃_Δ}` provides
order-`N^{gh}_F` Hessian accuracy of `F` at `x0`.

**Formalization Note.** Order-∞ function accuracy with constant `0` is the equality of model and
function at the point (p.6). `∇f₁` is the Jacobian and `∇²f₁` the second derivative
`ℝ^d →L[ℝ] ℝ^d →L[ℝ] ℝ^m`, each with its operator norm. `Mgt₁`, `Mht₁` are `M_{∇f̃₁}(x0)`,
`M_{∇²f̃₁}(x0)` (uniform bounds at `x0`); `Mgt₂`, `Mht₂` are `M_{∇f̃₂}(f₁(x0))`, `M_{∇²f̃₂}(f₁(x0))`
(uniform bounds at `f₁(x0)`), stated as hypotheses (Corollary 5). `hm₁`, `hm₂` state that the model
Hessians exist (`ContDiffAt`: every `C²` model qualifies). -/
theorem theorem_33 {d m : ℕ} (f₁ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m))
    (f₂ : EuclideanSpace ℝ (Fin m) → ℝ)
    (fm₁ : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m))
    (fm₂ : ℝ → EuclideanSpace ℝ (Fin m) → ℝ) (x0 : EuclideanSpace ℝ (Fin d))
    (Δbar Ng₁ Ng₂ Nh₁ Nh₂ κg₁ κg₂ κh₁ κh₂ Mgt₁ Mht₁ Mgt₂ Mht₂ NF K : ℝ)
    (hΔbar : 0 < Δbar) (hf₁ : ContDiff ℝ 2 f₁) (hf₂ : ContDiff ℝ 2 f₂)
    (hm₁ : ∀ Δ ∈ Set.Ioc 0 Δbar, ContDiffAt ℝ 2 (fm₁ Δ) x0)
    (hm₂ : ∀ Δ ∈ Set.Ioc 0 Δbar, ContDiffAt ℝ 2 (fm₂ Δ) (f₁ x0))
    (he₁ : ∀ Δ ∈ Set.Ioc 0 Δbar, fm₁ Δ x0 = f₁ x0)
    (he₂ : ∀ Δ ∈ Set.Ioc 0 Δbar, fm₂ Δ (f₁ x0) = f₂ (f₁ x0))
    (hg₁ : VecGradAccAt f₁ fm₁ x0 Δbar Ng₁ κg₁)
    (hh₁ : VecHessAccAt f₁ fm₁ x0 Δbar Nh₁ κh₁)
    (hg₂ : GradAccAt f₂ fm₂ (f₁ x0) Δbar Ng₂ κg₂)
    (hh₂ : HessAccAt f₂ fm₂ (f₁ x0) Δbar Nh₂ κh₂)
    (hMgt₁ : ∀ Δ ∈ Set.Ioc 0 Δbar, ‖fderiv ℝ (fm₁ Δ) x0‖ ≤ Mgt₁)
    (hMht₁ : ∀ Δ ∈ Set.Ioc 0 Δbar, ‖fderiv ℝ (fderiv ℝ (fm₁ Δ)) x0‖ ≤ Mht₁)
    (hMgt₂ : ∀ Δ ∈ Set.Ioc 0 Δbar, ‖fderiv ℝ (fm₂ Δ) (f₁ x0)‖ ≤ Mgt₂)
    (hMht₂ : ∀ Δ ∈ Set.Ioc 0 Δbar, ‖fderiv ℝ (fderiv ℝ (fm₂ Δ)) (f₁ x0)‖ ≤ Mht₂)
    (hNF : NF = min (min Ng₁ Ng₂) (min Nh₁ Nh₂))
    (hK : K = Mht₂ * (‖fderiv ℝ f₁ x0‖ + Mgt₁) * κg₁ * Δbar ^ (Ng₁ - NF)
        + Mht₁ * κg₂ * Δbar ^ (Ng₂ - NF)
        + (‖fderiv ℝ f₂ (f₁ x0)‖ + Mgt₂) * κh₁ * Δbar ^ (Nh₁ - NF)
        + ‖fderiv ℝ f₁ x0‖ ^ 2 * κh₂ * Δbar ^ (Nh₂ - NF)) :
    (∀ Δ ∈ Set.Ioc 0 Δbar,
      ‖fderiv ℝ (fderiv ℝ (fun x => f₂ (f₁ x))) x0
          - fderiv ℝ (fderiv ℝ (fun x => fm₂ Δ (fm₁ Δ x))) x0‖
        ≤ K * Δ ^ NF) ∧
    ∃ κ, HessAccAt (fun x => f₂ (f₁ x)) (fun Δ x => fm₂ Δ (fm₁ Δ x)) x0 Δbar NF κ := by sorry

end SurrogateOps.Supplement
