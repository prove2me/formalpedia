-- Prove2me | Theorems.Thm_SupportVectorMachines_Classification_theorem_6_24_instance_hinge_loss_v2
-- name    : SupportVectorMachines.Classification.theorem_6_24_instance_hinge_loss_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:43:33.03274+00:00
-- url     : https://prove2.me/theorems/57de1928-8803-4aed-a79e-8bfd5ad054c6
-- title:
--   Theorem 6.24 instance — oracle inequality for hinge-loss SVMs ($Y = \{-1,1\}$, separable RKHS)
-- statement:
--   This is the hinge-loss instance of Theorem 6.24 (Oracle inequality for SVMs) of Steinwart & Christmann, *Support Vector Machines* (Springer 2008, p. 224), as invoked in the proof of Theorem 8.1 (p. 289).
--
--   Let $L := L_{\mathrm{hinge}}$, $Y := \{-1,1\}$, $H$ be a separable RKHS of a measurable kernel $k$ over $X$ with $\|k\|_\infty \le 1$, and $P$ a distribution on $X \times Y$. Then for all $\lambda > 0$, $n \ge 1$, $\tau > 0$, with $P^n$-probability at least $1 - e^{-\tau}$,
--   $$
--   \lambda\|f_{D,\lambda}\|_H^2 + R_{L,P}(f_{D,\lambda}) - R^*_{L,P,H} < A_2(\lambda) + \lambda^{-1}\Big(\sqrt{\tfrac{8\tau}{n}} + \sqrt{\tfrac{4}{n} + \tfrac{8\tau}{3n}}\Big),
--   $$
--   where $f_{D,\lambda}$ is the SVM decision function for the sample $D$ and $A_2$ the approximation error function. The general Theorem 6.24 carries the factor $|L|_{\lambda^{-1/2},1}$, the Lipschitz constant of $L(y,\cdot)$ on $[-\lambda^{-1/2},\lambda^{-1/2}]$; for the hinge loss on $Y = \{-1,1\}$ it equals $1$, the simplification Theorem 8.1's proof uses.
--
--   **Formalization Note.** The retired version let $P$ be any probability measure on $X \times \mathbb R$: for a rare large label the hinge loss is $|y|$-Lipschitz, the true risk of $f_{D,\lambda}$ is huge and a small sample cannot see it (the accepted disproof). The corrected statement adds the standing convention $Y = \{-1,1\}$ as $P(X \times \{-1,1\}) = 1$ and the book's hypothesis that $H$ is separable (omitted in the retired version). $\|k\|_\infty \le 1$ is `∀ x, k x x ≤ 1`; `IsRKHSOfKernel` includes the measurability of $k(\cdot,x)$ (Lemma 4.24). $f_{D,\lambda}$ is any selection `fSVM D` of minimizers of $\lambda\|g\|_H^2 + R_{L,D}(g)$ (the minimizer is unique, so this is the book's object); the probability is the $n$-fold product measure `Measure.pi`, understood as the outer measure if the event is not measurable, as in the book. Risks are $[0,\infty]$-valued Lebesgue integrals of the bundled measurable nonnegative loss, $R^*_{L,P,H}$ and $A_2(\lambda)$ are infima in $[0,\infty]$, and the inequality is stated in $[0,\infty]$ (every quantity is finite here: $R_{L,P}(f) \le 1 + \|f\|_H$ and $R^*_{L,P,H} \le R_{L,P}(0) = 1$), so the retired integrability guard is unnecessary.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 224, Theorem 6.24 (instantiated for the hinge loss as in the proof of Theorem 8.1, p. 289)

import Mathlib
import Definitions.Def_SupportVectorMachines_Classification_RiskBasics_v2
import Definitions.Def_SupportVectorMachines_Classification_ClassificationLosses_v2
import Definitions.Def_SupportVectorMachines_Classification_RKHSAndSVM_v2

open MeasureTheory

namespace SupportVectorMachines.Classification

/-- The hinge-loss instance of Theorem 6.24 (Oracle inequality for SVMs), Steinwart & Christmann,
*Support Vector Machines*, Springer 2008, p. 224, used inside the proof of Theorem 8.1 (p. 289):
for `L := L_hinge`, `Y := {-1,1}` (binary classification; `P` is supported on `X × {-1,1}`), `H` a
separable RKHS of a measurable kernel `k` with `‖k‖∞ ≤ 1` (i.e. `∀ x, k x x ≤ 1`), and `P` a
distribution on `X × Y`, for all `λ > 0`, `n ≥ 1`, `τ > 0`, with `Pⁿ`-probability at least
`1 - e^{-τ}`,
`λ‖f_{D,λ}‖²_H + R_{L,P}(f_{D,λ}) - R*_{L,P,H} < A2(λ) + λ⁻¹(√(8τ/n) + √(4/n + 8τ/(3n)))`,
risks in `[0,∞]` (all finite here). The general theorem's Lipschitz-constant factor
`|L|_{λ^{-1/2},1}` is instantiated to `1`, the hinge loss's own (global) Lipschitz constant on
`Y = {-1,1}`, matching the simplification Theorem 8.1's proof uses.
Corrected version of `theorem_6_24_instance_hinge_loss`, which allowed arbitrary real labels
(for which the hinge loss is not `1`-Lipschitz and the bound fails), omitted the separability of
`H`, and used real-valued (junk-at-non-integrable) risks. -/
theorem theorem_6_24_instance_hinge_loss_v2 {X : Type*} [MeasurableSpace X]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (hkBdd : ∀ x, k x x ≤ 1)
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (hY : P (Set.univ ×ˢ ({-1, 1} : Set ℝ)) = 1)
    (n : ℕ) (hn : 0 < n) (lam : ℝ) (hlam : 0 < lam) (τ : ℝ) (hτ : 0 < τ)
    (fSVM : (Fin n → X × ℝ) → H)
    (hfSVM : ∀ D, IsSVMSolution H toFun hingeLoss lam n D (fSVM D)) :
    1 - Real.exp (-τ) ≤ (Measure.pi (fun _ : Fin n => P)).real
      {D | ENNReal.ofReal (lam * ‖fSVM D‖ ^ 2) + risk hingeLoss P (toFun (fSVM D)) -
          restrictedBayesRisk H toFun hingeLoss P <
        approxErrorA2 H toFun hingeLoss P lam +
          ENNReal.ofReal (lam⁻¹ *
            (Real.sqrt (8 * τ / n) + Real.sqrt (4 / n + 8 * τ / (3 * n))))} := by sorry

end SupportVectorMachines.Classification
