-- Prove2me | Theorems.Thm_SupportVectorMachines_InfiniteSample_lemma_5_1_uniqueness_of_svm_solutions
-- name    : SupportVectorMachines.InfiniteSample.lemma_5_1_uniqueness_of_svm_solutions
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T23:04:47.339118+00:00
-- url     : https://prove2.me/theorems/88080838-6e9a-4a64-a609-8e1aea7d1724
-- title:
--   Lemma 5.1 — uniqueness of general SVM solutions
-- statement:
--   This is Lemma 5.1 of Steinwart & Christmann, *Support Vector Machines* (Springer 2008,
--   p. 167): let $L : X \times Y \times \mathbb R \to [0,\infty)$ be a convex loss, $H$ be the
--   RKHS of a measurable kernel over $X$, and $P$ be a distribution on $X \times Y$ with
--   $R_{L,P}(f) < \infty$ for some $f \in H$. Then for all $\lambda > 0$ there exists at most one
--   **general SVM solution** $f_{P,\lambda}$, i.e. at most one minimizer of
--
--   $$
--   f \mapsto \lambda\|f\|_H^2 + R_{L,P}(f)
--   $$
--
--   over $H$.
--
--   This is the population (infinite-sample) half of the existence-and-uniqueness picture this
--   mission develops toward the representer theorem: the finiteness hypothesis rules out the
--   trivial case where every $f \in H$ has infinite risk, in which case the objective would be
--   constantly $+\infty$ and every $f$ would (vacuously) be a minimizer, so the proof's convexity
--   argument (a strict-convexity computation for the midpoint of two hypothetical minimizers)
--   could not distinguish them.
--
--   **Formalization Note** The two minimizer hypotheses are stated for two arbitrary candidates
--   `f1 f2 : H`, and the conclusion is `f1 = f2` — the direct Lean rendering of "at most one".
--   `R_{L,P}$ is `populationRisk` (an `ENNReal`-valued lower integral, so no integrability
--   hypothesis is needed beyond the one finiteness witness the book itself states).
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 167, Lemma 5.1

import Mathlib
import Definitions.Def_SupportVectorMachines_InfiniteSample_Loss
import Definitions.Def_SupportVectorMachines_InfiniteSample_IsRKHSOfKernel
import Definitions.Def_SupportVectorMachines_InfiniteSample_populationRisk

open MeasureTheory

namespace SupportVectorMachines.InfiniteSample

/-- Lemma 5.1 (Uniqueness of SVM solutions), p. 167: let `L` be a convex loss, `H` be the RKHS of
a (measurable) kernel `k` over `X`, and `P` be a distribution on `X × ℝ` with `R_{L,P}(f) < ∞` for
some `f ∈ H`. Then for all `λ > 0` there is at most one general SVM solution, i.e. at most one
minimizer of `f ↦ λ‖f‖²_H + R_{L,P}(f)` over `H`. -/
theorem lemma_5_1_uniqueness_of_svm_solutions {X : Type*} [MeasurableSpace X]
    (L : Loss X) (hL : ∀ x y, ConvexOn ℝ Set.univ (L x y)) (hLnn : ∀ x y t, 0 ≤ L x y t)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (hfin : ∃ f : H, populationRisk L P (toFun f) < ⊤)
    (lam : ℝ) (hlam : 0 < lam) (f1 f2 : H)
    (hf1 : ∀ g : H, ENNReal.ofReal (lam * ‖f1‖ ^ 2) + populationRisk L P (toFun f1) ≤
      ENNReal.ofReal (lam * ‖g‖ ^ 2) + populationRisk L P (toFun g))
    (hf2 : ∀ g : H, ENNReal.ofReal (lam * ‖f2‖ ^ 2) + populationRisk L P (toFun f2) ≤
      ENNReal.ofReal (lam * ‖g‖ ^ 2) + populationRisk L P (toFun g)) :
    f1 = f2 := by sorry

end SupportVectorMachines.InfiniteSample
