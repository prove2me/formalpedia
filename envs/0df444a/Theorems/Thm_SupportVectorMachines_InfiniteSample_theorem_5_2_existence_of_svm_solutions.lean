-- Prove2me | Theorems.Thm_SupportVectorMachines_InfiniteSample_theorem_5_2_existence_of_svm_solutions
-- name    : SupportVectorMachines.InfiniteSample.theorem_5_2_existence_of_svm_solutions
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T23:05:31.718131+00:00
-- url     : https://prove2.me/theorems/733d4b41-33c6-4570-a6b2-3c5b0ecd5afa
-- title:
--   Theorem 5.2 — existence of general SVM solutions
-- statement:
--   This is Theorem 5.2 of Steinwart & Christmann, *Support Vector Machines* (Springer 2008,
--   p. 167): let $L : X \times Y \times \mathbb R \to [0,\infty)$ be a convex loss and $P$ be a
--   distribution on $X \times Y$ such that $L$ is a $P$-integrable Nemitski loss. Let $H$ be the
--   RKHS of a bounded measurable kernel over $X$. Then for all $\lambda > 0$ there exists a
--   general SVM solution $f_{P,\lambda} \in H$, i.e. a minimizer of
--
--   $$
--   f \mapsto \lambda\|f\|_H^2 + R_{L,P}(f)
--   $$
--
--   over $H$.
--
--   Together with Lemma 5.1, this gives existence and uniqueness of $f_{P,\lambda}$ for every
--   convex, $P$-integrable-Nemitski loss and every bounded-kernel RKHS — the population analogue
--   of the representer theorem's own existence-and-uniqueness clause, and the template the
--   representer theorem's proof explicitly reuses ("existence can be shown as in the proof of
--   Theorem 5.2").
--
--   **Formalization Note** The boundedness of the kernel is rendered as a uniform bound on the
--   diagonal, $\exists M, \forall x, k(x,x) \le M$ — the book's own notion of a bounded kernel
--   ($\sup_x k(x,x) < \infty$, used to embed $H$ continuously into $L^\infty$). The convexity of
--   $L$ is not used to establish existence in the book's own remark following the proof, but is
--   kept as a hypothesis for fidelity to the theorem's exact statement.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 167, Theorem 5.2

import Mathlib
import Definitions.Def_SupportVectorMachines_InfiniteSample_Loss
import Definitions.Def_SupportVectorMachines_InfiniteSample_NemitskiLoss
import Definitions.Def_SupportVectorMachines_InfiniteSample_IsRKHSOfKernel
import Definitions.Def_SupportVectorMachines_InfiniteSample_populationRisk

open MeasureTheory

namespace SupportVectorMachines.InfiniteSample

/-- Theorem 5.2 (Existence of SVM solutions), p. 167: let `L` be a convex loss and `P` be a
distribution on `X × ℝ` such that `L` is a `P`-integrable Nemitski loss. Let `H` be the RKHS of a
bounded (measurable) kernel `k` over `X`. Then for all `λ > 0` there exists a general SVM
solution, i.e. a minimizer of `f ↦ λ‖f‖²_H + R_{L,P}(f)` over `H`. -/
theorem theorem_5_2_existence_of_svm_solutions {X : Type*} [MeasurableSpace X]
    (L : Loss X) (hL : ∀ x y, ConvexOn ℝ Set.univ (L x y)) (hLnn : ∀ x y t, 0 ≤ L x y t)
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P] (hNem : PIntegrableNemitskiLoss L P)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (hkBdd : ∃ M : ℝ, ∀ x : X, k x x ≤ M)
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ f : H, ∀ g : H, ENNReal.ofReal (lam * ‖f‖ ^ 2) + populationRisk L P (toFun f) ≤
      ENNReal.ofReal (lam * ‖g‖ ^ 2) + populationRisk L P (toFun g) := by sorry

end SupportVectorMachines.InfiniteSample
