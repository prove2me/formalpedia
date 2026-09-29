-- Prove2me | Theorems.Thm_SupportVectorMachines_Classification_theorem_8_1_oracle_inequality_classification
-- name    : SupportVectorMachines.Classification.theorem_8_1_oracle_inequality_classification
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T23:12:56.250258+00:00
-- url     : https://prove2.me/theorems/afe0a314-8c56-4600-9020-6772bc0ea78f
-- title:
--   Theorem 8.1 — oracle inequality for classifying with support vector machines
-- statement:
--   This is Theorem 8.1 (Oracle inequality for classification) of Steinwart & Christmann,
--   *Support Vector Machines* (Springer 2008, p. 289), the payoff result this mission series
--   builds toward: an explicit, non-asymptotic bound on how close an SVM classifier's
--   classification risk gets to the Bayes risk.
--
--   Let $L$ be the hinge loss, $Y := \{-1,1\}$, $H$ be a separable RKHS with bounded measurable
--   kernel $k$ over $X$ satisfying $\|k\|_\infty \le 1$, and $P$ be a distribution on $X\times Y$
--   such that $H$ is dense in $L^1(P_X)$. Then, for all $\lambda > 0$, $n \ge 1$, and $\tau > 0$,
--   we have with $P^n$-probability at least $1 - e^{-\tau}$ that
--   $$
--   R_{L_{\mathrm{class}},P}(f_{D,\lambda}) - R^*_{L_{\mathrm{class}},P} < A_2(\lambda) +
--     \lambda^{-1}\left(\sqrt{\tfrac{8\tau}{n}} + \sqrt{\tfrac{4}{n} + \tfrac{8\tau}{3n}}\right),
--   $$
--   where $A_2(\cdot)$ is the approximation error function with respect to $L$, $H$, and $P$.
--
--   The left-hand side is the *classification* risk even though the SVM itself is trained using
--   the (convex, tractable) hinge loss — this is exactly what justifies the hinge loss as a
--   surrogate: making the right-hand side small (e.g. by letting $\lambda \to 0$ as $n \to
--   \infty$) forces the SVM's classification risk toward the Bayes risk. The proof combines three
--   earlier results, each restated locally as its own milestone in this mission: the hinge-loss
--   instance of Theorem 6.24 (an oracle inequality for the regularized hinge risk), the
--   hinge-loss instance of Theorem 5.31 (identifying $R^*_{L,P,H}$ with the unrestricted Bayes
--   hinge risk $R^*_{L,P}$, via $H$'s density in $L^1(P_X)$), and the instance of Theorem 2.31
--   / Zhang's inequality (passing from the excess hinge risk to the excess classification risk).
--
--   **Formalization Note** $\|k\|_\infty \le 1$ is rendered as `∀ x, k x x ≤ 1` (Eq. (4.15):
--   $\|k\|_\infty := \sup_x \sqrt{k(x,x)}$, so $\|k\|_\infty \le 1 \iff \sup_x k(x,x) \le 1$) — a
--   load-bearing hypothesis, not a normalization convenience: it is what makes the Theorem 6.24
--   instance's Lipschitz-constant factor collapse to $1$, producing the "8" and "4" constants
--   verbatim. $H$ separable is `TopologicalSpace.SeparableSpace H`. "With $P^n$-probability at
--   least $1-e^{-\tau}$" is `Measure.pi (fun _ : Fin n => P)`, the $n$-fold product measure, and
--   the bound is stated as a lower bound `1 - exp(-τ) ≤ (Measure.pi ...).real {D | ...}` on the
--   measure of the event, not as an a.s. or expectation statement. $A_2(\lambda)$ is not left as
--   an opaque symbol: it is `approxErrorA2`, the genuine, non-trivial quantity of Definition 5.14
--   depending jointly on $H$, $L$, $P$ and $\lambda$ (`RKHSAndSVM` definition item). Theorem 8.2
--   (the benign-kernels specialization of Theorem 8.1, using entropy-number/covering-number
--   machinery this chapter's other results do not need) is out of scope for this mission per the
--   budget in `STATUS.md` — a complete goal plus the three milestones it actually invokes beats a
--   wider mission that never compiled the extra apparatus. As in the Theorem 6.24 instance, `hInt`
--   and `hIntClass` guard the real-valued (junk-at-non-integrable) hinge and classification risks
--   of `fSVM D` against the junk value; both are automatic under `‖k‖∞ ≤ 1` and are stated
--   explicitly rather than silently assumed.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 289, Theorem 8.1

import Mathlib
import Definitions.Def_SupportVectorMachines_Classification_RiskBasics
import Definitions.Def_SupportVectorMachines_Classification_ClassificationLosses
import Definitions.Def_SupportVectorMachines_Classification_RKHSAndSVM

open MeasureTheory

namespace SupportVectorMachines.Classification

/-- Theorem 8.1 (Oracle inequality for classification), p. 289: let `L` be the hinge loss,
`Y := {-1,1}`, `H` be a separable RKHS with bounded measurable kernel `k` over `X` satisfying
`‖k‖∞ ≤ 1`, and `P` be a distribution on `X × Y` such that `H` is dense in `L¹(PX)`. Then for all
`λ > 0`, `n ≥ 1`, `τ > 0`, with `Pⁿ`-probability at least `1 - e^{-τ}`,
`R_{L_class,P}(f_{D,λ}) - R*_{L_class,P} < A2(λ) + λ⁻¹(√(8τ/n) + √(4/n + 8τ/(3n)))`, where `A2` is
the approximation error function with respect to `L`, `H`, `P`. -/
theorem theorem_8_1_oracle_inequality_classification {X : Type*} [MeasurableSpace X]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (hkBdd : ∀ x, k x x ≤ 1)
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (hY : P (Set.univ ×ˢ ({-1, 1} : Set ℝ)) = 1)
    (hDense : DenseInL1 H toFun (P.map Prod.fst))
    (n : ℕ) (hn : 0 < n) (lam : ℝ) (hlam : 0 < lam) (τ : ℝ) (hτ : 0 < τ)
    (fSVM : (Fin n → X × ℝ) → H)
    (hfSVM : ∀ D, IsSVMSolution H toFun hingeLoss lam n D (fSVM D))
    (hInt : ∀ D, Integrable (fun p : X × ℝ => hingeLoss p.1 p.2 (toFun (fSVM D) p.1)) P)
    (hIntClass : ∀ D, Integrable (fun p : X × ℝ => classLoss p.1 p.2 (toFun (fSVM D) p.1)) P) :
    1 - Real.exp (-τ) ≤ (Measure.pi (fun _ : Fin n => P)).real
      {D | risk classLoss P (toFun (fSVM D)) - bayesRisk classLoss P <
        approxErrorA2 H toFun hingeLoss P lam +
          lam⁻¹ * (Real.sqrt (8 * τ / n) + Real.sqrt (4 / n + 8 * τ / (3 * n)))} := by sorry

end SupportVectorMachines.Classification
