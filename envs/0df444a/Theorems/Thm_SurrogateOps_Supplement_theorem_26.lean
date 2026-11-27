-- Prove2me | Theorems.Thm_SurrogateOps_Supplement_theorem_26
-- name    : SurrogateOps.Supplement.theorem_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:42:06.115442+00:00
-- url     : https://prove2.me/theorems/a39aba1b-849a-593d-adb6-caa2507daea4
-- title:
--   Theorem 26, p.17 (corrected: $\bar\Delta$ chosen as in Lemma 21) — a quotient of two models accurate near $x_0$ has Hessian accuracy of order $\min\{N^f_i,N^g_i,N^h_i\}$ near $x_0$
-- statement:
--   Let $f_1,f_2:\mathbb R^d\to\mathbb R$ be $C^2$, $F=f_1/f_2$ and $\tilde F_\Delta=\tilde f_{1,\Delta}/\tilde f_{2,\Delta}$, with $f_2(x)\neq0$ and $\tilde f_{2,\Delta}(x)\neq0$ for all $\Delta\in(0,\bar\Delta]$ and $x\in B_\Delta(x_0)$, and let $M_{1/f_2}(x_0)$ bound $|1/f_2|$ on $B_{\bar\Delta}(x_0)$. Suppose that for $i=1,2$ the class $\{\tilde f_{i,\Delta}\}_{(0,\bar\Delta]}$ provides order-$N^f_i$ function accuracy (constant $\kappa^f_i$), order-$N^g_i$ gradient accuracy and order-$N^h_i$ Hessian accuracy of $f_i$ near $x_0$, and that $N^f_2>0$. Let $N^{fgh}_F=\min\{N^f_1,N^f_2,N^g_1,N^g_2,N^h_1,N^h_2\}$. Then:
--
--   1. some $\Delta_0\in(0,\bar\Delta]$ satisfies $\Delta_0^{N^f_2}M_{1/f_2}(x_0)\kappa^f_2<1$;
--   2. for every such $\Delta_0$, the class $\{\tilde F_\Delta\}_{(0,\Delta_0]}$ provides order-$N^{fgh}_F$ Hessian accuracy for $F$ near $x_0$.
--
--   **Formalization Note** As in Theorem 24, item 1 is the "sufficiently small $\bar\Delta$" of Lemma 21. The models are assumed twice differentiable around every point of $B_\Delta(x_0)$.
--
--   Differences from the source:
--   - encoding: the space ℝ^d, the closed ball B_Δ(x₀), a class of models {f̃_Δ}_{(0,Δ̄]} → EuclideanSpace ℝ (Fin d), Metric.closedBall x0 Δ, a map ℝ → E → ℝ used only on Set.Ioc 0 Δbar; reason: Lean convention; same instances
--   - encoding: the gradient ∇f and its Euclidean norm → fderiv ℝ f with the operator norm of E →L[ℝ] ℝ; reason: on EuclideanSpace the two norms agree by Riesz representation; same instances
--   - encoding: the Hessian ∇²f as a matrix → fderiv ℝ (fderiv ℝ f) as a bilinear map; reason: the matrix and the second derivative determine each other; same instances
--   - reading: ‖·‖ on Hessians is unspecified → the operator norm of E →L[ℝ] E →L[ℝ] ℝ; reason: the spectral norm is the standard matrix norm in this literature and the one the proof's ‖ab^⊤‖ = ‖a‖‖b‖ uses; on a matrix it equals the operator norm of the bilinear map
--   - encoding: provides order-N accuracy: ∃ κ ≥ 0 → the constant κ is an explicit argument of the predicate, with 0 ≤ N and 0 ≤ κ as clauses; the order clause of the conclusion is ∃ κ; reason: a universally quantified κ in a hypothesis is the same as an existential one; the conclusion's κ depends on neither Δ nor x
--   - encoding: standing assumption of §4 (p.12): f₂(x) ≠ 0 and f̃_{2,Δ}(x) ≠ 0 for all Δ ∈ (0, Δ̄] and x ∈ B_Δ(x₀) → the hypothesis hne; reason: copied from the section's standing assumption; it is needed in Lean, where x / 0 = 0
--   - encoding: M_{1/f₂}(x₀), the bound of |1/f₂| on B_Δ̄(x₀) (p.12) → a number M with |1 / f₂ x| ≤ M for all x ∈ closedBall x0 Δbar; reason: the page names the bound without fixing it; a continuous f₂ without zeros on the compact ball always has one
--   - reading: ∇²f̃_{i,Δ}(x) is used without stating the regularity of the models → ContDiffAt ℝ 2 (fm_i Δ) x for every Δ ∈ (0, Δ̄] and every x ∈ B_Δ(x₀); reason: the page's ∇²f̃_{i,Δ}(x) presupposes it; Lean's fderiv is 0 at a non-differentiable point, where the product, quotient and chain rules fail
--   - encoding: min{…} of finitely many orders → nested binary min of the reals; reason: same value
--   - correction: the conclusion on the given (0, Δ̄], whose Δ̄ is only implicitly the "sufficiently small Δ̄" of Lemma 21 → (a) some Δ₀ ∈ (0, Δ̄] has Δ₀^{N^f_2} M_{1/f₂}(x₀) κ^f_2(x₀) < 1, and (b) for every such Δ₀ the conclusion holds for the class on (0, Δ₀], with Δ₀ in place of Δ̄; reason: counterexample on the given interval: d = 1, x₀ = 0, Δ̄ = 1, f₂ = 1, f̃_{2,Δ} ≡ c(Δ) with c = 1 for Δ < 1/4 and at Δ = 1/2, c = |Δ − 1/2| otherwise (order-1 function accuracy with κ = 4, exact derivatives, c never 0), f̃₁ = f₁ ∈ {1, x, x²}: the function, gradient, Hessian error of the quotient is a multiple of |1 − 1/c(Δ)|, unbounded as Δ → 1/2; the inequality is the one the proof of Lemma 21 imposes (p.13), and (a) keeps every instance of the source
-- source:
--   Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Theorem 26, p.17; Lemma 21, p.13; standing assumptions of §4, p.12

import Mathlib
import Definitions.Def_SurrogateOps_FunAccNear
import Definitions.Def_SurrogateOps_GradAccNear
import Definitions.Def_SurrogateOps_HessAccNear

namespace SurrogateOps.Supplement

/-- **Theorem 26 (Hessian accuracy near `x0`), for `Δ̄` chosen as in Lemma 21.** Chen, Hare,
Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models,
arXiv:2112.08411v1, Theorem 26, p.17 (with Lemma 21, p.13, and the standing assumptions of §4, p.12).
For `F = f₁/f₂`, `F̃_Δ = f̃_{1,Δ}/f̃_{2,Δ}` with function, gradient and Hessian accuracy of both
classes near `x0` and `N^f_2 > 0`: (a) some `Δ₀ ∈ (0, Δ̄]` satisfies `Δ₀^{N^f_2} M_{1/f₂} κ^f_2 < 1`,
and (b) for every such `Δ₀`, `{F̃_Δ}_{(0,Δ₀]}` provides order-`N^{fgh}_F` Hessian accuracy of `F` near
`x0`, `N^{fgh}_F = min{N^f_1, N^f_2, N^g_1, N^g_2, N^h_1, N^h_2}`.

**Formalization Note.** As in Theorem 24: the "sufficiently small `Δ̄`" of Lemma 21 is (a), with `Δ₀`
for the chosen `Δ̄`; on an arbitrary `(0, Δ̄]` the conclusion is false (`MODERATION_NOTES.md`). `M` is
`M_{1/f₂}(x0)`. `hne` is the standing assumption of §4; `hm₁`, `hm₂` state that `∇²f̃_{i,Δ}` exists on
`B_Δ(x0)` (`ContDiffAt`: every `C²` model qualifies). -/
theorem theorem_26 {d : ℕ} (f₁ f₂ : EuclideanSpace ℝ (Fin d) → ℝ)
    (fm₁ fm₂ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (x0 : EuclideanSpace ℝ (Fin d))
    (Δbar Nf₁ Nf₂ Ng₁ Ng₂ Nh₁ Nh₂ κf₁ κf₂ κg₁ κg₂ κh₁ κh₂ M NF : ℝ)
    (hΔbar : 0 < Δbar) (hf₁ : ContDiff ℝ 2 f₁) (hf₂ : ContDiff ℝ 2 f₂)
    (hne : ∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ, f₂ x ≠ 0 ∧ fm₂ Δ x ≠ 0)
    (hM : ∀ x ∈ Metric.closedBall x0 Δbar, |1 / f₂ x| ≤ M)
    (hm₁ : ∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ, ContDiffAt ℝ 2 (fm₁ Δ) x)
    (hm₂ : ∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ, ContDiffAt ℝ 2 (fm₂ Δ) x)
    (hfa₁ : FunAccNear f₁ fm₁ x0 Δbar Nf₁ κf₁) (hfa₂ : FunAccNear f₂ fm₂ x0 Δbar Nf₂ κf₂)
    (hg₁ : GradAccNear f₁ fm₁ x0 Δbar Ng₁ κg₁) (hg₂ : GradAccNear f₂ fm₂ x0 Δbar Ng₂ κg₂)
    (hh₁ : HessAccNear f₁ fm₁ x0 Δbar Nh₁ κh₁) (hh₂ : HessAccNear f₂ fm₂ x0 Δbar Nh₂ κh₂)
    (hN₂ : 0 < Nf₂)
    (hNF : NF = min (min (min Nf₁ Nf₂) (min Ng₁ Ng₂)) (min Nh₁ Nh₂)) :
    (∃ Δ₀ ∈ Set.Ioc 0 Δbar, Δ₀ ^ Nf₂ * M * κf₂ < 1) ∧
    ∀ Δ₀ ∈ Set.Ioc 0 Δbar, Δ₀ ^ Nf₂ * M * κf₂ < 1 →
      ∃ κ, HessAccNear (fun x => f₁ x / f₂ x) (fun Δ x => fm₁ Δ x / fm₂ Δ x) x0 Δ₀ NF κ := by sorry

end SurrogateOps.Supplement
