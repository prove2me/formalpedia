-- Prove2me | Theorems.Thm_SurrogateOps_Supplement_theorem_31
-- name    : SurrogateOps.Supplement.theorem_31
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:43:28.604149+00:00
-- url     : https://prove2.me/theorems/ccec8fca-514f-47d1-9a47-157c7fa218cb
-- title:
--   Theorem 31, p.20 — gradient accuracy at $x_0$ of a composition of models exact at $x_0$ and $f_1(x_0)$, with the explicit constant $K^g_F(x_0)$
-- statement:
--   Let $f_1:\mathbb R^d\to\mathbb R^m$ and $f_2:\mathbb R^m\to\mathbb R$ be $C^1$, $F=f_2\circ f_1$ and $\tilde F_\Delta=\tilde f_{2,\Delta}\circ\tilde f_{1,\Delta}$. Suppose $\tilde f_{1,\Delta}(x_0)=f_1(x_0)$ and $\{\tilde f_{1,\Delta}\}_{(0,\bar\Delta]}$ provides order-$N^g_1$ gradient accuracy of $f_1$ at $x_0$ with constant $\kappa^g_1(x_0)$, and $\tilde f_{2,\Delta}(f_1(x_0))=f_2(f_1(x_0))$ and $\{\tilde f_{2,\Delta}\}_{(0,\bar\Delta]}$ provides order-$N^g_2$ gradient accuracy of $f_2$ at $f_1(x_0)$ with constant $\kappa^g_2(f_1(x_0))$. Let $M_{\nabla\tilde f_1}(x_0)$ bound $\|\nabla\tilde f_{1,\Delta}(x_0)\|$ uniformly in $\Delta$ and $N^g_F=\min\{N^g_1,N^g_2\}$. Then for every $\Delta\in(0,\bar\Delta]$
--
--   $$
--   \|\nabla F(x_0)-\nabla\tilde F_\Delta(x_0)\|\le K^g_F(x_0)\Delta^{N^g_F},\qquad
--   K^g_F(x_0)=\|\nabla f_2(f_1(x_0))\|\kappa^g_1(x_0)\bar\Delta^{N^g_1-N^g_F}+M_{\nabla\tilde f_1}(x_0)\kappa^g_2(f_1(x_0))\bar\Delta^{N^g_2-N^g_F}.
--   $$
--
--   In particular $\{\tilde F_\Delta\}_{(0,\bar\Delta]}$ provides order-$N^g_F$ gradient accuracy of $F$ at $x_0$.
--
--   **Formalization Note** $\nabla f_1$ is the Jacobian with its operator norm. The models are assumed differentiable at $x_0$ and at $f_1(x_0)$ respectively.
--
--   Differences from the source:
--   - encoding: f₁ : ℝ^d → ℝ^m, f₂ : ℝ^m → ℝ, the closed balls, classes of models of f₁ and f₂ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m), EuclideanSpace ℝ (Fin m) → ℝ, Metric.closedBall, maps ℝ → E → G used only on Set.Ioc 0 Δbar; accuracy of f₁ by the vector-valued predicates SurrogateOps.Supplement.Vec*; reason: Lean convention; the vector-valued predicates are Definition 1 with the norm of ℝ^m; same instances
--   - encoding: the gradient ∇f and its Euclidean norm → fderiv ℝ f with the operator norm of E →L[ℝ] ℝ; reason: on EuclideanSpace the two norms agree by Riesz representation; same instances
--   - reading: ‖∇f₁‖ and ‖∇²f₁‖ for the vector-valued map f₁ are unspecified → the operator norms of the Jacobian fderiv ℝ f₁ x : ℝ^d →L[ℝ] ℝ^m and of fderiv ℝ (fderiv ℝ f₁) x : ℝ^d →L[ℝ] ℝ^d →L[ℝ] ℝ^m; reason: the proof's estimates ‖∇f₁^⊤ v‖ ≤ ‖∇f₁‖‖v‖ hold for the operator norm; a componentwise norm would change the constants
--   - encoding: provides order-N accuracy: ∃ κ ≥ 0 → the constant κ is an explicit argument of the predicate, with 0 ≤ N and 0 ≤ κ as clauses; the order clause of the conclusion is ∃ κ; reason: a universally quantified κ in a hypothesis is the same as an existential one; the conclusion's κ depends on neither Δ nor x
--   - encoding: order-∞ function accuracy at a point with constant 0 → equality of model and function at that point for every Δ ∈ (0, Δ̄]; reason: the page states the equivalence itself (p.6)
--   - reading: ∇f̃_{1,Δ}(x₀), ∇f̃_{2,Δ}(f₁(x₀)) is used without stating the regularity of the models → DifferentiableAt ℝ (fm₁ Δ) x0 and DifferentiableAt ℝ (fm₂ Δ) (f₁ x0) for every Δ ∈ (0, Δ̄] at x₀ and at f₁(x₀); reason: the page's ∇f̃_{1,Δ}(x₀), ∇f̃_{2,Δ}(f₁(x₀)) presupposes it; Lean's fderiv is 0 at a non-differentiable point, where the product, quotient and chain rules fail
--   - encoding: min{…} of finitely many orders → nested binary min of the reals; reason: same value
--   - encoding: the constant K(x₀) → a variable fixed by an equation hypothesis (or written out in the conclusion); reason: same as the page's "Let" and "where"
--   - encoding: M-bounds M_{∇f̃₁}(x₀) → numbers with bounding hypotheses on ‖∇f̃_{1,Δ}(x₀)‖ for Δ ∈ (0, Δ̄]; reason: the page says "we use … to denote these bounds" (p.4); the theorem holds for every valid choice, and no sSup junk value can enter
-- source:
--   Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Theorem 31, p.20; standing assumptions of §5, p.18

import Mathlib
import Definitions.Def_SurrogateOps_GradAccAt
import Definitions.Def_SurrogateOps_Supplement_VecGradAccAt

namespace SurrogateOps.Supplement

/-- **Theorem 31 (Gradient accuracy at `x0`).** Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate
Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Theorem 31, p.20 (standing
assumptions of §5, p.18).
For `f₁ : ℝ^d → ℝ^m`, `f₂ : ℝ^m → ℝ` in `C¹`, `F = f₂ ∘ f₁`, `F̃_Δ = f̃_{2,Δ} ∘ f̃_{1,Δ}`, models
exact at `x0` and at `f₁(x0)` respectively, and `N^g_F = min{N^g_1, N^g_2}`:
`‖∇F(x0) - ∇F̃_Δ(x0)‖ ≤ K Δ^{N^g_F}` with
`K = ‖∇f₂(f₁(x0))‖ κ^g_1 Δ̄^{N^g_1 - N^g_F} + M_{∇f̃₁}(x0) κ^g_2 Δ̄^{N^g_2 - N^g_F}`, and `{F̃_Δ}` provides
order-`N^g_F` gradient accuracy of `F` at `x0`.

**Formalization Note.** Order-∞ function accuracy with constant `0` is the equality of model and
function at the point (p.6). `∇f₁` is the Jacobian `fderiv ℝ f₁ x0 : ℝ^d →L[ℝ] ℝ^m` with its operator
norm. `Mgt₁` is `M_{∇f̃₁}(x0)`, a uniform bound of `‖∇f̃_{1,Δ}(x0)‖` (Corollary 5), stated as a
hypothesis. `hm₁`, `hm₂` state that the model derivatives at `x0` and `f₁(x0)` exist. -/
theorem theorem_31 {d m : ℕ} (f₁ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m))
    (f₂ : EuclideanSpace ℝ (Fin m) → ℝ)
    (fm₁ : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m))
    (fm₂ : ℝ → EuclideanSpace ℝ (Fin m) → ℝ) (x0 : EuclideanSpace ℝ (Fin d))
    (Δbar Ng₁ Ng₂ κg₁ κg₂ Mgt₁ NF K : ℝ)
    (hΔbar : 0 < Δbar) (hf₁ : ContDiff ℝ 1 f₁) (hf₂ : ContDiff ℝ 1 f₂)
    (hm₁ : ∀ Δ ∈ Set.Ioc 0 Δbar, DifferentiableAt ℝ (fm₁ Δ) x0)
    (hm₂ : ∀ Δ ∈ Set.Ioc 0 Δbar, DifferentiableAt ℝ (fm₂ Δ) (f₁ x0))
    (he₁ : ∀ Δ ∈ Set.Ioc 0 Δbar, fm₁ Δ x0 = f₁ x0)
    (he₂ : ∀ Δ ∈ Set.Ioc 0 Δbar, fm₂ Δ (f₁ x0) = f₂ (f₁ x0))
    (hg₁ : VecGradAccAt f₁ fm₁ x0 Δbar Ng₁ κg₁)
    (hg₂ : GradAccAt f₂ fm₂ (f₁ x0) Δbar Ng₂ κg₂)
    (hMgt₁ : ∀ Δ ∈ Set.Ioc 0 Δbar, ‖fderiv ℝ (fm₁ Δ) x0‖ ≤ Mgt₁)
    (hNF : NF = min Ng₁ Ng₂)
    (hK : K = ‖fderiv ℝ f₂ (f₁ x0)‖ * κg₁ * Δbar ^ (Ng₁ - NF) + Mgt₁ * κg₂ * Δbar ^ (Ng₂ - NF)) :
    (∀ Δ ∈ Set.Ioc 0 Δbar,
      ‖fderiv ℝ (fun x => f₂ (f₁ x)) x0 - fderiv ℝ (fun x => fm₂ Δ (fm₁ Δ x)) x0‖
        ≤ K * Δ ^ NF) ∧
    ∃ κ, GradAccAt (fun x => f₂ (f₁ x)) (fun Δ x => fm₂ Δ (fm₁ Δ x)) x0 Δbar NF κ := by sorry

end SurrogateOps.Supplement
