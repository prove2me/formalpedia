-- Prove2me | Theorems.Thm_SupportVectorMachines_Classification_theorem_6_24_instance_hinge_loss
-- name    : SupportVectorMachines.Classification.theorem_6_24_instance_hinge_loss
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T23:10:53.114118+00:00
-- url     : https://prove2.me/theorems/7afdd7a9-3ea9-428d-82ff-1a43b1ede7e4
-- title:
--   Theorem 6.24 instance — oracle inequality for hinge-loss SVMs
-- statement:
--   This is the hinge-loss instance of Theorem 6.24 (Oracle inequality for SVMs) of Steinwart &
--   Christmann, *Support Vector Machines* (Springer 2008, p. 224), exactly as invoked in the
--   proof of Theorem 8.1 ("Obviously, $L := L_{\mathrm{hinge}}$ is a convex and Lipschitz
--   continuous loss satisfying $L(y,0)=1$ ... Therefore, Theorem 6.24 shows that ...").
--
--   Let $L := L_{\mathrm{hinge}}$, $H$ be a separable RKHS with measurable kernel $k$ satisfying
--   $\|k\|_\infty \le 1$, and $P$ a distribution on $X \times Y$. Then for all $\lambda > 0$,
--   $n \ge 1$, $\tau > 0$, with $P^n$-probability at least $1 - e^{-\tau}$,
--   $$
--   \lambda \|f_{D,\lambda}\|_H^2 + R_{L,P}(f_{D,\lambda}) - R^*_{L,P,H} < A_2(\lambda) +
--     \lambda^{-1}\left(\sqrt{\tfrac{8\tau}{n}} + \sqrt{\tfrac{4}{n} + \tfrac{8\tau}{3n}}\right).
--   $$
--
--   The general Theorem 6.24 carries an extra factor $|L|_{\lambda^{-1/2},1}$, the local
--   Lipschitz constant of $L$ on $[-\lambda^{-1/2},\lambda^{-1/2}]$; for the hinge loss this
--   constant is exactly $1$ everywhere (the hinge loss is globally $1$-Lipschitz), which is the
--   simplification Theorem 8.1's proof uses to drop it from the bound entirely.
--
--   **Formalization Note** `IsSVMSolution` encodes "$f_{D,\lambda}$ minimizes
--   $g \mapsto \lambda\|g\|_H^2 + R_{L,D}(g)$ over $H$" directly as the hypothesis on `fSVM D`,
--   rather than re-deriving existence/uniqueness (`04-representer`'s Theorem 5.2/Lemma 5.1
--   territory, out of scope here per Hard Rule 9). The probability is stated on the product
--   measure `Measure.pi (fun _ : Fin n => P)` on `Fin n → X × ℝ`, matching the book's `Pⁿ`.
--   `risk`/`restrictedBayesRisk`/`approxErrorA2` are real-valued (junk-at-non-integrable) Bochner
--   integrals/infima (as in `01-loss-functions`), so `hInt` guards the hinge risk of `fSVM D`
--   against that junk value — automatic under `‖k‖∞ ≤ 1` (bounded predictions on a probability
--   space) but not implied by the Lean types alone, so it is stated explicitly rather than
--   silently assumed.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 224, Theorem 6.24 (instantiated for the hinge loss as in the proof of Theorem 8.1, p. 289)

import Mathlib
import Definitions.Def_SupportVectorMachines_Classification_RiskBasics
import Definitions.Def_SupportVectorMachines_Classification_ClassificationLosses
import Definitions.Def_SupportVectorMachines_Classification_RKHSAndSVM

open MeasureTheory

namespace SupportVectorMachines.Classification

/-- The hinge-loss instance of Theorem 6.24 (Oracle inequality for SVMs), p. 224, used inside the
proof of Theorem 8.1: for `L := L_hinge`, `H` a separable RKHS of a measurable kernel `k` with
`‖k‖∞ ≤ 1` (i.e. `∀ x, k x x ≤ 1`), and `P` a distribution on `X × Y`, for all `λ > 0`, `n ≥ 1`,
`τ > 0`, with `Pⁿ`-probability at least `1 - e^{-τ}`,
`λ‖f_{D,λ}‖²_H + R_{L,P}(f_{D,λ}) - R*_{L,P,H} < A2(λ) + λ⁻¹(√(8τ/n) + √(4/n + 8τ/(3n)))`. The
general theorem's Lipschitz-constant factor `|L|_{λ^{-1/2},1}` is instantiated to `1`, the hinge
loss's own (global) Lipschitz constant, matching the simplification Theorem 8.1's proof uses. -/
theorem theorem_6_24_instance_hinge_loss {X : Type*} [MeasurableSpace X]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (hkBdd : ∀ x, k x x ≤ 1)
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 0 < n) (lam : ℝ) (hlam : 0 < lam) (τ : ℝ) (hτ : 0 < τ)
    (fSVM : (Fin n → X × ℝ) → H)
    (hfSVM : ∀ D, IsSVMSolution H toFun hingeLoss lam n D (fSVM D))
    (hInt : ∀ D, Integrable (fun p : X × ℝ => hingeLoss p.1 p.2 (toFun (fSVM D) p.1)) P) :
    1 - Real.exp (-τ) ≤ (Measure.pi (fun _ : Fin n => P)).real
      {D | lam * ‖fSVM D‖ ^ 2 + risk hingeLoss P (toFun (fSVM D)) -
          restrictedBayesRisk H toFun hingeLoss P <
        approxErrorA2 H toFun hingeLoss P lam +
          lam⁻¹ * (Real.sqrt (8 * τ / n) + Real.sqrt (4 / n + 8 * τ / (3 * n)))} := by sorry

end SupportVectorMachines.Classification
