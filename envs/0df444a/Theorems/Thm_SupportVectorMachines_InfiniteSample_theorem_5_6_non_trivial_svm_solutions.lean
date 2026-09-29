-- Prove2me | Theorems.Thm_SupportVectorMachines_InfiniteSample_theorem_5_6_non_trivial_svm_solutions
-- name    : SupportVectorMachines.InfiniteSample.theorem_5_6_non_trivial_svm_solutions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T23:06:24.896063+00:00
-- url     : https://prove2.me/theorems/0fdccd52-8c66-4f50-8874-d8d17be92c12
-- title:
--   Theorem 5.6 — non-trivial SVM solutions
-- statement:
--   This is Theorem 5.6 of Steinwart & Christmann, *Support Vector Machines* (Springer 2008,
--   p. 168): let $L : X \times Y \times \mathbb R \to [0,\infty)$ be a convex loss and $P$ be a
--   distribution on $X \times Y$ such that $L$ is a $P$-integrable Nemitski loss. Let $H$ be the
--   RKHS of a bounded measurable kernel over $X$ such that
--
--   $$
--   R^*_{L,P,H} := \inf_{f \in H} R_{L,P}(f) \; < \; R_{L,P}(0).
--   $$
--
--   Then, for all $\lambda > 0$, every general SVM solution $f_{P,\lambda} \ne 0$.
--
--   This rules out the degenerate case where regularization drives the solution all the way to
--   the zero function: it happens exactly when $H$ can already do no better than predicting a
--   constant zero, which the gap condition excludes. The theorem is what justifies treating SVM
--   decision functions as genuinely data/model-dependent objects rather than a regularization
--   artifact.
--
--   **Formalization Note** The general SVM solution $f_{P,\lambda}$ is taken as an arbitrary
--   element of $H$ satisfying the minimizer property (rather than re-deriving its existence,
--   which is Theorem 5.2's content); by Lemma 5.1 it is in any case unique, so quantifying over an
--   arbitrary minimizer is exactly the book's own "for all $\lambda > 0$, $f_{P,\lambda} \ne 0$".
--   $R^*_{L,P,H}$ is rendered as `⨅ f : H, populationRisk L P (toFun f)`, an infimum in `ENNReal`
--   that is always well-defined (no boundedness or nonemptiness hypothesis needed).
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 168, Theorem 5.6

import Mathlib
import Definitions.Def_SupportVectorMachines_InfiniteSample_Loss
import Definitions.Def_SupportVectorMachines_InfiniteSample_NemitskiLoss
import Definitions.Def_SupportVectorMachines_InfiniteSample_IsRKHSOfKernel
import Definitions.Def_SupportVectorMachines_InfiniteSample_populationRisk

open MeasureTheory

namespace SupportVectorMachines.InfiniteSample

/-- Theorem 5.6 (Non-trivial SVM solutions), p. 168: let `L` be a convex loss and `P` be a
distribution on `X × ℝ` such that `L` is a `P`-integrable Nemitski loss. Let `H` be the RKHS of a
bounded (measurable) kernel `k` over `X` with `R*_{L,P,H} := inf_{f∈H} R_{L,P}(f) < R_{L,P}(0)`.
Then for all `λ > 0`, every general SVM solution `f_{P,λ}` is nonzero. -/
theorem theorem_5_6_non_trivial_svm_solutions {X : Type*} [MeasurableSpace X]
    (L : Loss X) (hL : ∀ x y, ConvexOn ℝ Set.univ (L x y)) (hLnn : ∀ x y t, 0 ≤ L x y t)
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P] (hNem : PIntegrableNemitskiLoss L P)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (hkBdd : ∃ M : ℝ, ∀ x : X, k x x ≤ M)
    (hgap : (⨅ f : H, populationRisk L P (toFun f)) < populationRisk L P (fun _ => 0))
    (lam : ℝ) (hlam : 0 < lam) (fPlam : H)
    (hmin : ∀ g : H, ENNReal.ofReal (lam * ‖fPlam‖ ^ 2) + populationRisk L P (toFun fPlam) ≤
      ENNReal.ofReal (lam * ‖g‖ ^ 2) + populationRisk L P (toFun g)) :
    fPlam ≠ 0 := by sorry

end SupportVectorMachines.InfiniteSample
