-- Prove2me | Theorems.Thm_SurrogateOps_theorem_12
-- name    : SurrogateOps.theorem_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:51:29.897679+00:00
-- url     : https://prove2.me/theorems/d55722a4-efed-4727-9b92-e2bd77775be0
-- title:
--   Theorem 12, pp.7–8 — Hessian accuracy of a product of two models exact at $x_0$
-- statement:
--   Let $f_1,f_2:\mathbb R^d\to\mathbb R$ be $C^2$, with $F=f_1f_2$ and $\tilde F_\Delta=\tilde f_{1,\Delta}\tilde f_{2,\Delta}$. Suppose that for $i=1,2$ and all $\Delta\in(0,\bar\Delta]$ the model satisfies $\tilde f_{i,\Delta}(x_0)=f_i(x_0)$, and that $\{\tilde f_{i,\Delta}\}_{(0,\bar\Delta]}$ provides order-$N^g_i$ gradient accuracy with constant $\kappa^g_i(x_0)$ and order-$N^h_i$ Hessian accuracy with constant $\kappa^h_i(x_0)$ of $f_i$ at $x_0$. Let $N^{gh}_F=\min\{N^g_1,N^g_2,N^h_1,N^h_2\}$. Let $M_{\nabla f_i}(x_0)$ bound $\|\nabla f_i\|$ on $B_{\bar\Delta}(x_0)$ and let $M_{\nabla\tilde f_i}(x_0)$ bound $\|\nabla\tilde f_{i,\Delta}(x_0)\|$ uniformly in $\Delta$. Then for every $\Delta\in(0,\bar\Delta]$
--
--   $$
--   \|\nabla^2F(x_0)-\nabla^2\tilde F_\Delta(x_0)\|\le K^h_F(x_0)\Delta^{N^{gh}_F},
--   $$
--
--   where
--
--   $$
--   \begin{aligned}
--   K^h_F(x_0)={}&(M_{\nabla f_2}+M_{\nabla\tilde f_2})\kappa^g_1\bar\Delta^{N^g_1-N^{gh}_F}+(M_{\nabla f_1}+M_{\nabla\tilde f_1})\kappa^g_2\bar\Delta^{N^g_2-N^{gh}_F}\\
--   &+|f_2(x_0)|\kappa^h_1\bar\Delta^{N^h_1-N^{gh}_F}+|f_1(x_0)|\kappa^h_2\bar\Delta^{N^h_2-N^{gh}_F}.
--   \end{aligned}
--   $$
--
--   In particular $\{\tilde F_\Delta\}_{(0,\bar\Delta]}$ provides order-$N^{gh}_F$ Hessian accuracy for $F$ at $x_0$.
--
--   This is the two-factor case of Theorem 19.
--
--   Differences from the source:
--   - encoding: the space ℝ^d, the closed ball B_Δ(x₀), a class of models {f̃_Δ}_{(0,Δ̄]} → EuclideanSpace ℝ (Fin d), Metric.closedBall x0 Δ, a map ℝ → E → ℝ used only on Set.Ioc 0 Δbar; reason: Lean convention; same instances
--   - encoding: the gradient ∇f and its Euclidean norm → fderiv ℝ f with the operator norm of E →L[ℝ] ℝ; reason: on EuclideanSpace the two norms agree by Riesz representation; same instances
--   - encoding: the Hessian ∇²f as a matrix → fderiv ℝ (fderiv ℝ f) as a bilinear map; reason: the matrix and the second derivative determine each other; same instances
--   - reading: ‖·‖ on Hessians is unspecified → the operator norm of E →L[ℝ] E →L[ℝ] ℝ; reason: the spectral norm is the standard matrix norm in this literature and the one the proof's ‖ab^⊤‖ = ‖a‖‖b‖ uses; on a matrix it equals the operator norm of the bilinear map
--   - encoding: provides order-N accuracy: ∃ κ ≥ 0 → the constant κ is an explicit argument of the predicate, with 0 ≤ N and 0 ≤ κ as clauses; reason: the theorems name the constant κ_i(x₀); the order clause of the conclusion is ∃ κ
--   - encoding: order-∞ function accuracy at x₀ with constant κ^f_i(x₀) = 0 → fm i Δ x0 = f i x0 for every Δ ∈ (0, Δ̄]; reason: the page states the equivalence itself (p.6)
--   - reading: ∇²f̃_{i,Δ}(x₀) is used without stating the regularity of the models → ContDiffAt ℝ 2 (fm i Δ) x0 for every Δ ∈ (0, Δ̄]; reason: the page's ∇²f̃_{i,Δ}(x₀) presupposes it; every C² model qualifies; Lean's fderiv is 0 at a non-differentiable point, where the product rule fails
--   - encoding: N^{gh}_F and K^h_F(x₀) → the number is a variable fixed by an equation or IsLeast hypothesis; reason: same as the page's "Let" and "where"
--   - encoding: M-bounds: M_{∇f_i}(x₀), M_{∇f̃_i}(x₀) → numbers with hypotheses on ‖∇f_i‖ over B_Δ̄(x₀) and on ‖∇f̃_{i,Δ}(x₀)‖ for Δ ∈ (0, Δ̄]; reason: the page says "we use … to denote these bounds"; the theorem holds for every valid choice, and no sSup junk value can enter
-- source:
--   Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Theorem 12, pp.7–8

import Mathlib
import Definitions.Def_SurrogateOps_GradAccAt
import Definitions.Def_SurrogateOps_HessAccAt

namespace SurrogateOps

/-- **Theorem 12 (Hessian accuracy at `x0`).** Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on
Sub-models, arXiv:2112.08411v1, Theorem 12, pp.7–8.
For `F = f₁f₂`, `F̃_Δ = f̃_{1,Δ}f̃_{2,Δ}`, models exact at `x0` and
`N = min{N^g_1, N^g_2, N^h_1, N^h_2}`: `‖∇²F(x0) - ∇²F̃_Δ(x0)‖ ≤ K Δ^N` with `K` the constant of the
page, and `{F̃_Δ}` provides order-`N` Hessian accuracy of `F` at `x0`.

**Formalization Note.** Order-∞ function accuracy at `x0` with constant `0` is the equality
`fm Δ x0 = f x0` (p.6). `∇²f̃_Δ(x0)` must exist for the page's statement to make sense; `hm₁`, `hm₂`
state that (`ContDiffAt`: every `C²` model qualifies). `Mg₁`, `Mg₂` bound `‖∇f₁‖`, `‖∇f₂‖` on `B_Δ̄(x0)`
(p.4). `Mgt₁`, `Mgt₂` are the uniform bounds of `‖∇f̃_Δ(x0)‖` (Corollary 5). They are hypotheses rather
than `sSup`s, so the theorem holds for every valid choice. -/
theorem theorem_12 {d : ℕ} (f₁ f₂ : EuclideanSpace ℝ (Fin d) → ℝ)
    (fm₁ fm₂ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (x0 : EuclideanSpace ℝ (Fin d))
    (Δbar Ng₁ Ng₂ Nh₁ Nh₂ κg₁ κg₂ κh₁ κh₂ Mg₁ Mg₂ Mgt₁ Mgt₂ NF K : ℝ)
    (hΔbar : 0 < Δbar) (hf₁ : ContDiff ℝ 2 f₁) (hf₂ : ContDiff ℝ 2 f₂)
    (hm₁ : ∀ Δ ∈ Set.Ioc 0 Δbar, ContDiffAt ℝ 2 (fm₁ Δ) x0)
    (hm₂ : ∀ Δ ∈ Set.Ioc 0 Δbar, ContDiffAt ℝ 2 (fm₂ Δ) x0)
    (he₁ : ∀ Δ ∈ Set.Ioc 0 Δbar, fm₁ Δ x0 = f₁ x0)
    (he₂ : ∀ Δ ∈ Set.Ioc 0 Δbar, fm₂ Δ x0 = f₂ x0)
    (hg₁ : GradAccAt f₁ fm₁ x0 Δbar Ng₁ κg₁)
    (hg₂ : GradAccAt f₂ fm₂ x0 Δbar Ng₂ κg₂)
    (hh₁ : HessAccAt f₁ fm₁ x0 Δbar Nh₁ κh₁)
    (hh₂ : HessAccAt f₂ fm₂ x0 Δbar Nh₂ κh₂)
    (hMg₁ : ∀ x ∈ Metric.closedBall x0 Δbar, ‖fderiv ℝ f₁ x‖ ≤ Mg₁)
    (hMg₂ : ∀ x ∈ Metric.closedBall x0 Δbar, ‖fderiv ℝ f₂ x‖ ≤ Mg₂)
    (hMgt₁ : ∀ Δ ∈ Set.Ioc 0 Δbar, ‖fderiv ℝ (fm₁ Δ) x0‖ ≤ Mgt₁)
    (hMgt₂ : ∀ Δ ∈ Set.Ioc 0 Δbar, ‖fderiv ℝ (fm₂ Δ) x0‖ ≤ Mgt₂)
    (hNF : NF = min (min Ng₁ Ng₂) (min Nh₁ Nh₂))
    (hK : K = (Mg₂ + Mgt₂) * κg₁ * Δbar ^ (Ng₁ - NF)
        + (Mg₁ + Mgt₁) * κg₂ * Δbar ^ (Ng₂ - NF)
        + |f₂ x0| * κh₁ * Δbar ^ (Nh₁ - NF)
        + |f₁ x0| * κh₂ * Δbar ^ (Nh₂ - NF)) :
    (∀ Δ ∈ Set.Ioc 0 Δbar,
      ‖fderiv ℝ (fderiv ℝ (fun x => f₁ x * f₂ x)) x0
          - fderiv ℝ (fderiv ℝ (fun x => fm₁ Δ x * fm₂ Δ x)) x0‖
        ≤ K * Δ ^ NF) ∧
    ∃ κ, HessAccAt (fun x => f₁ x * f₂ x) (fun Δ x => fm₁ Δ x * fm₂ Δ x) x0 Δbar NF κ := by sorry

end SurrogateOps
