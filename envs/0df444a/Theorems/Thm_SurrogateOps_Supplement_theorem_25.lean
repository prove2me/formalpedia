-- Prove2me | Theorems.Thm_SurrogateOps_Supplement_theorem_25
-- name    : SurrogateOps.Supplement.theorem_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:41:43.277923+00:00
-- url     : https://prove2.me/theorems/8cbf2a13-db55-46ac-95b9-16932a0e198a
-- title:
--   Theorem 25, p.16 — Hessian accuracy at $x_0$ of a quotient of two models exact at $x_0$, with the explicit constant $K^h_F(x_0)$
-- statement:
--   Let $f_1,f_2:\mathbb R^d\to\mathbb R$ be $C^2$, $F=f_1/f_2$ and $\tilde F_\Delta=\tilde f_{1,\Delta}/\tilde f_{2,\Delta}$, with $f_2(x)\neq0$ and $\tilde f_{2,\Delta}(x)\neq0$ for all $\Delta\in(0,\bar\Delta]$ and $x\in B_\Delta(x_0)$. Suppose that for $i=1,2$ the models are exact at $x_0$ and $\{\tilde f_{i,\Delta}\}_{(0,\bar\Delta]}$ provides order-$N^g_i$ gradient accuracy and order-$N^h_i$ Hessian accuracy of $f_i$ at $x_0$ with constants $\kappa^g_i(x_0)$, $\kappa^h_i(x_0)$. Let $M_{\nabla f_i}(x_0)$ bound $\|\nabla f_i\|$ on $B_{\bar\Delta}(x_0)$, let $M_{\nabla\tilde f_i}(x_0)$ bound $\|\nabla\tilde f_{i,\Delta}(x_0)\|$ uniformly in $\Delta$, and let $N^{gh}_F=\min\{N^g_1,N^g_2,N^h_1,N^h_2\}$. Then for every $\Delta\in(0,\bar\Delta]$, $\|\nabla^2F(x_0)-\nabla^2\tilde F_\Delta(x_0)\|\le K^h_F(x_0)\Delta^{N^{gh}_F}$, where (all quantities at $x_0$)
--
--   $$
--   \begin{aligned}
--   K^h_F={}&\Bigl|\frac1{f_2^2}\Bigr|(M_{\nabla f_2}+M_{\nabla\tilde f_2})\kappa^g_1\bar\Delta^{N^g_1-N^{gh}_F}
--   +\Bigl[\Bigl|\frac1{f_2^2}\Bigr|(M_{\nabla f_1}+M_{\nabla\tilde f_1})+\Bigl|\frac{2f_1}{f_2^3}\Bigr|(M_{\nabla f_2}+M_{\nabla\tilde f_2})\Bigr]\kappa^g_2\bar\Delta^{N^g_2-N^{gh}_F}\\
--   &+\Bigl|\frac1{f_2}\Bigr|\kappa^h_1\bar\Delta^{N^h_1-N^{gh}_F}+\Bigl|\frac{f_1}{f_2^2}\Bigr|\kappa^h_2\bar\Delta^{N^h_2-N^{gh}_F}.
--   \end{aligned}
--   $$
--
--   In particular $\{\tilde F_\Delta\}_{(0,\bar\Delta]}$ provides order-$N^{gh}_F$ Hessian accuracy for $F$ at $x_0$.
--
--   **Formalization Note** The models are assumed twice differentiable around $x_0$ (`ContDiffAt ℝ 2`).
--
--   Differences from the source:
--   - encoding: the space ℝ^d, the closed ball B_Δ(x₀), a class of models {f̃_Δ}_{(0,Δ̄]} → EuclideanSpace ℝ (Fin d), Metric.closedBall x0 Δ, a map ℝ → E → ℝ used only on Set.Ioc 0 Δbar; reason: Lean convention; same instances
--   - encoding: the gradient ∇f and its Euclidean norm → fderiv ℝ f with the operator norm of E →L[ℝ] ℝ; reason: on EuclideanSpace the two norms agree by Riesz representation; same instances
--   - encoding: the Hessian ∇²f as a matrix → fderiv ℝ (fderiv ℝ f) as a bilinear map; reason: the matrix and the second derivative determine each other; same instances
--   - reading: ‖·‖ on Hessians is unspecified → the operator norm of E →L[ℝ] E →L[ℝ] ℝ; reason: the spectral norm is the standard matrix norm in this literature and the one the proof's ‖ab^⊤‖ = ‖a‖‖b‖ uses; on a matrix it equals the operator norm of the bilinear map
--   - encoding: provides order-N accuracy: ∃ κ ≥ 0 → the constant κ is an explicit argument of the predicate, with 0 ≤ N and 0 ≤ κ as clauses; the order clause of the conclusion is ∃ κ; reason: a universally quantified κ in a hypothesis is the same as an existential one; the conclusion's κ depends on neither Δ nor x
--   - encoding: order-∞ function accuracy at a point with constant 0 → equality of model and function at that point for every Δ ∈ (0, Δ̄]; reason: the page states the equivalence itself (p.6)
--   - encoding: standing assumption of §4 (p.12): f₂(x) ≠ 0 and f̃_{2,Δ}(x) ≠ 0 for all Δ ∈ (0, Δ̄] and x ∈ B_Δ(x₀) → the hypothesis hne; reason: copied from the section's standing assumption; it is needed in Lean, where x / 0 = 0
--   - reading: ∇²f̃_{i,Δ}(x₀) is used without stating the regularity of the models → ContDiffAt ℝ 2 (fm_i Δ) x0 for every Δ ∈ (0, Δ̄] at x₀; reason: the page's ∇²f̃_{i,Δ}(x₀) presupposes it; Lean's fderiv is 0 at a non-differentiable point, where the product, quotient and chain rules fail
--   - encoding: min{…} of finitely many orders → nested binary min of the reals; reason: same value
--   - encoding: the constant K(x₀) → a variable fixed by an equation hypothesis (or written out in the conclusion); reason: same as the page's "Let" and "where"
--   - encoding: M-bounds M_{∇f_i}(x₀), M_{∇f̃_i}(x₀) → numbers with bounding hypotheses on ‖∇f_i‖ over B_Δ̄(x₀) and on ‖∇f̃_{i,Δ}(x₀)‖ for Δ ∈ (0, Δ̄]; reason: the page says "we use … to denote these bounds" (p.4); the theorem holds for every valid choice, and no sSup junk value can enter
-- source:
--   Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Theorem 25, p.16; standing assumptions of §4, p.12

import Mathlib
import Definitions.Def_SurrogateOps_GradAccAt
import Definitions.Def_SurrogateOps_HessAccAt

namespace SurrogateOps.Supplement

/-- **Theorem 25 (Hessian accuracy at `x0`).** Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate
Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Theorem 25, p.16 (standing
assumptions of §4, p.12).
For `F = f₁/f₂`, `F̃_Δ = f̃_{1,Δ}/f̃_{2,Δ}`, models exact at `x0` and
`N^{gh}_F = min{N^g_1, N^g_2, N^h_1, N^h_2}`: `‖∇²F(x0) - ∇²F̃_Δ(x0)‖ ≤ K Δ^{N^{gh}_F}` with `K` the
constant of the page, and `{F̃_Δ}` provides order-`N^{gh}_F` Hessian accuracy of `F` at `x0`.

**Formalization Note.** Order-∞ function accuracy at `x0` with constant `0` is the equality
`fm Δ x0 = f x0` (p.6). `hne` is the standing assumption of §4. `∇²f̃_{i,Δ}(x0)` must exist; `hm₁`,
`hm₂` state that (`ContDiffAt`: every `C²` model qualifies). `Mg₁`, `Mg₂` are `M_{∇f_i}(x0)`, bounds of
`‖∇f_i‖` on `B_Δ̄(x0)` (p.4); `Mgt₁`, `Mgt₂` are `M_{∇f̃_i}(x0)`, uniform bounds of `‖∇f̃_{i,Δ}(x0)‖`
(Corollary 5). They are hypotheses rather than `sSup`s. -/
theorem theorem_25 {d : ℕ} (f₁ f₂ : EuclideanSpace ℝ (Fin d) → ℝ)
    (fm₁ fm₂ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (x0 : EuclideanSpace ℝ (Fin d))
    (Δbar Ng₁ Ng₂ Nh₁ Nh₂ κg₁ κg₂ κh₁ κh₂ Mg₁ Mg₂ Mgt₁ Mgt₂ NF K : ℝ)
    (hΔbar : 0 < Δbar) (hf₁ : ContDiff ℝ 2 f₁) (hf₂ : ContDiff ℝ 2 f₂)
    (hne : ∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ, f₂ x ≠ 0 ∧ fm₂ Δ x ≠ 0)
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
    (hK : K = |1 / f₂ x0 ^ 2| * (Mg₂ + Mgt₂) * κg₁ * Δbar ^ (Ng₁ - NF)
        + (|1 / f₂ x0 ^ 2| * (Mg₁ + Mgt₁) + |2 * f₁ x0 / f₂ x0 ^ 3| * (Mg₂ + Mgt₂))
            * κg₂ * Δbar ^ (Ng₂ - NF)
        + |1 / f₂ x0| * κh₁ * Δbar ^ (Nh₁ - NF)
        + |f₁ x0 / f₂ x0 ^ 2| * κh₂ * Δbar ^ (Nh₂ - NF)) :
    (∀ Δ ∈ Set.Ioc 0 Δbar,
      ‖fderiv ℝ (fderiv ℝ (fun x => f₁ x / f₂ x)) x0
          - fderiv ℝ (fderiv ℝ (fun x => fm₁ Δ x / fm₂ Δ x)) x0‖
        ≤ K * Δ ^ NF) ∧
    ∃ κ, HessAccAt (fun x => f₁ x / f₂ x) (fun Δ x => fm₁ Δ x / fm₂ Δ x) x0 Δbar NF κ := by sorry

end SurrogateOps.Supplement
