-- Prove2me | Theorems.Thm_SupportVectorMachines_InfiniteSample_lemma_5_1_uniqueness_of_svm_solutions_v2
-- name    : SupportVectorMachines.InfiniteSample.lemma_5_1_uniqueness_of_svm_solutions_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:43:16.777743+00:00
-- url     : https://prove2.me/theorems/8247250f-76d0-4506-a1b6-c4996a226128
-- title:
--   Lemma 5.1 — uniqueness of general SVM solutions (measurable loss and kernel)
-- statement:
--   This is Lemma 5.1 of Steinwart & Christmann, *Support Vector Machines* (Springer 2008, p. 167): let $L : X \times Y \times \mathbb R \to [0,\infty)$ be a convex loss (Definition 2.1: measurable and nonnegative; $L(x,y,\cdot)$ convex for all $x,y$), $H$ the RKHS of a measurable kernel over $X$, and $P$ a distribution on $X \times Y$ with $R_{L,P}(f) < \infty$ for some $f \in H$. Then for every $\lambda > 0$ there exists at most one general SVM solution $f_{P,\lambda}$, i.e. at most one minimizer of
--   $$
--   f \mapsto \lambda\|f\|_H^2 + R_{L,P}(f)
--   $$
--   over $H$.
--
--   **Formalization Note.** The retired version quantified over the bare function type for $L$ and did not require the kernel to be measurable; for a non-measurable integrand the lower Lebesgue integral is superadditive but not convex in $f$, and two distinct minimizers existed (the accepted disproof). The corrected statement takes $L$ in the bundled `Loss X` (measurable and nonnegative, so the retired separate nonnegativity hypothesis is absorbed) and adds the measurability of the kernel, under which $R_{L,P}$ is the genuine convex risk. Uniqueness is rendered as: any two minimizers $f_1, f_2$ coincide. Conventions made explicit (common to the corrected Chapter 5 milestones): a loss is the bundled `Loss X` of Definition 2.1 — measurable on $X \times \mathbb R \times \mathbb R$ and nonnegative — with labels embedded in $\mathbb R$ (a distribution on $X \times Y$ is one on $X \times \mathbb R$); "$H$ is the RKHS of a measurable kernel $k$" is `IsRKHSOfKernel` (injective evaluation map, $k(\cdot,x) \in H$ and the reproducing property) together with the measurability of $k(\cdot,x)$ for every $x$ (the book's notion of a measurable kernel, Lemma 4.24, equivalent to all $f \in H$ being measurable); $R_{L,P}$ is the $[0,\infty]$-valued Lebesgue risk; the regularized objective $\lambda\|f\|_H^2 + R_{L,P}(f)$ is evaluated in $[0,\infty]$; and $H$ may live in any universe.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 167, Lemma 5.1

import Mathlib
import Definitions.Def_SupportVectorMachines_InfiniteSample_Loss_v2
import Definitions.Def_SupportVectorMachines_InfiniteSample_IsRKHSOfKernel
import Definitions.Def_SupportVectorMachines_InfiniteSample_populationRisk_v2

open MeasureTheory

namespace SupportVectorMachines.InfiniteSample

/-- Lemma 5.1 (Uniqueness of SVM solutions), Steinwart & Christmann, *Support Vector Machines*,
Springer 2008, p. 167: let `L : X × Y × ℝ → [0,∞)` be a convex loss (Definition 2.1: measurable
and nonnegative, bundled in `Loss X`; convex in `t` for every `x, y`), `H` be the RKHS of a
measurable kernel `k` over `X` (`k(·,x)` measurable for every `x`, Lemma 4.24), and `P` be a
distribution on `X × ℝ` with `R_{L,P}(f) < ∞` for some `f ∈ H`. Then for all `λ > 0` there is at
most one general SVM solution, i.e. at most one minimizer of `f ↦ λ‖f‖²_H + R_{L,P}(f)` over `H`.
Corrected version of `lemma_5_1_uniqueness_of_svm_solutions`, whose `Loss X` was the bare
function type (no measurability) and whose kernel was not required to be measurable, so the
risk was a non-convex lower integral and two distinct minimizers could exist. -/
theorem lemma_5_1_uniqueness_of_svm_solutions_v2 {X : Type*} [MeasurableSpace X]
    (L : Loss X) (hL : ∀ x y, ConvexOn ℝ Set.univ (L x y))
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (hk : ∀ x, Measurable (fun x' => k x' x))
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (hfin : ∃ f : H, populationRisk L P (toFun f) < ⊤)
    (lam : ℝ) (hlam : 0 < lam) (f1 f2 : H)
    (hf1 : ∀ g : H, ENNReal.ofReal (lam * ‖f1‖ ^ 2) + populationRisk L P (toFun f1) ≤
      ENNReal.ofReal (lam * ‖g‖ ^ 2) + populationRisk L P (toFun g))
    (hf2 : ∀ g : H, ENNReal.ofReal (lam * ‖f2‖ ^ 2) + populationRisk L P (toFun f2) ≤
      ENNReal.ofReal (lam * ‖g‖ ^ 2) + populationRisk L P (toFun g)) :
    f1 = f2 := by sorry

end SupportVectorMachines.InfiniteSample
