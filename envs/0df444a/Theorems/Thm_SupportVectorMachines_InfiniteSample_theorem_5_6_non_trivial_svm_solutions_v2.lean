-- Prove2me | Theorems.Thm_SupportVectorMachines_InfiniteSample_theorem_5_6_non_trivial_svm_solutions_v2
-- name    : SupportVectorMachines.InfiniteSample.theorem_5_6_non_trivial_svm_solutions_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:43:30.292551+00:00
-- url     : https://prove2.me/theorems/021abe8c-96c5-4428-94d5-91951a45b704
-- title:
--   Theorem 5.6 — non-trivial SVM solutions (measurable loss and kernel)
-- statement:
--   This is Theorem 5.6 of Steinwart & Christmann, *Support Vector Machines* (Springer 2008, p. 168): let $L : X \times Y \times \mathbb R \to [0,\infty)$ be a convex loss (Definition 2.1: measurable and nonnegative; convex in $t$) and $P$ a distribution on $X \times Y$ such that $L$ is a $P$-integrable Nemitski loss. Let $H$ be the RKHS of a bounded measurable kernel over $X$ such that
--   $$
--   R^*_{L,P,H} := \inf_{f \in H} R_{L,P}(f) < R_{L,P}(0).
--   $$
--   Then for every $\lambda > 0$ the general SVM solution satisfies $f_{P,\lambda} \ne 0$.
--
--   **Formalization Note.** The retired version quantified over the bare function type for $L$ and did not require the kernel to be measurable; the lower Lebesgue integral of a non-measurable integrand is not convex in $f$, and $0$ was a minimizer despite the gap (the accepted disproof). The corrected statement takes $L$ in the bundled `Loss X` (measurable and nonnegative) and adds the measurability of the kernel. The solution $f_{P,\lambda}$ is rendered as an arbitrary minimizer of $\lambda\|f\|_H^2 + R_{L,P}(f)$ (it exists and is unique by Theorem 5.2 and Lemma 5.1); $R^*_{L,P,H}$ is an infimum in $[0,\infty]$ and $R_{L,P}(0)$ the risk of the zero function. Conventions made explicit (common to the corrected Chapter 5 milestones): a loss is the bundled `Loss X` of Definition 2.1 — measurable on $X \times \mathbb R \times \mathbb R$ and nonnegative — with labels embedded in $\mathbb R$ (a distribution on $X \times Y$ is one on $X \times \mathbb R$); "$H$ is the RKHS of a measurable kernel $k$" is `IsRKHSOfKernel` (injective evaluation map, $k(\cdot,x) \in H$ and the reproducing property) together with the measurability of $k(\cdot,x)$ for every $x$ (the book's notion of a measurable kernel, Lemma 4.24, equivalent to all $f \in H$ being measurable); $R_{L,P}$ is the $[0,\infty]$-valued Lebesgue risk; the regularized objective $\lambda\|f\|_H^2 + R_{L,P}(f)$ is evaluated in $[0,\infty]$; and $H$ may live in any universe.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 168, Theorem 5.6

import Mathlib
import Definitions.Def_SupportVectorMachines_InfiniteSample_Loss_v2
import Definitions.Def_SupportVectorMachines_InfiniteSample_NemitskiLoss_v2
import Definitions.Def_SupportVectorMachines_InfiniteSample_IsRKHSOfKernel
import Definitions.Def_SupportVectorMachines_InfiniteSample_populationRisk_v2

open MeasureTheory

namespace SupportVectorMachines.InfiniteSample

/-- Theorem 5.6 (Non-trivial SVM solutions), Steinwart & Christmann, *Support Vector Machines*,
Springer 2008, p. 168: let `L` be a convex loss (Definition 2.1: measurable and nonnegative,
bundled in `Loss X`; convex in `t`) and `P` be a distribution on `X × ℝ` such that `L` is a
`P`-integrable Nemitski loss. Let `H` be the RKHS of a bounded measurable kernel `k` over `X`
(`sup_x k(x,x) < ∞`, `k(·,x)` measurable for every `x`) with
`R*_{L,P,H} := inf_{f∈H} R_{L,P}(f) < R_{L,P}(0)`. Then for all `λ > 0`, every general SVM
solution `f_{P,λ}` (a minimizer of `f ↦ λ‖f‖²_H + R_{L,P}(f)` over `H`) is nonzero.
Corrected version of `theorem_5_6_non_trivial_svm_solutions`, whose `Loss X` was the bare
function type (no measurability) and whose kernel was not required to be measurable, so the
risk was a non-convex lower integral and `0` could be a minimizer despite the gap. -/
theorem theorem_5_6_non_trivial_svm_solutions_v2 {X : Type*} [MeasurableSpace X]
    (L : Loss X) (hL : ∀ x y, ConvexOn ℝ Set.univ (L x y))
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P] (hNem : PIntegrableNemitskiLoss L P)
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (hk : ∀ x, Measurable (fun x' => k x' x))
    (hkBdd : ∃ M : ℝ, ∀ x : X, k x x ≤ M)
    (hgap : (⨅ f : H, populationRisk L P (toFun f)) < populationRisk L P (fun _ => 0))
    (lam : ℝ) (hlam : 0 < lam) (fPlam : H)
    (hmin : ∀ g : H, ENNReal.ofReal (lam * ‖fPlam‖ ^ 2) + populationRisk L P (toFun fPlam) ≤
      ENNReal.ofReal (lam * ‖g‖ ^ 2) + populationRisk L P (toFun g)) :
    fPlam ≠ 0 := by sorry

end SupportVectorMachines.InfiniteSample
