-- Prove2me | Theorems.Thm_UCalibDirichlet_lemma_2_1
-- name    : UCalibDirichlet.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:24:11.198338+00:00
-- url     : https://prove2.me/theorems/e79f3943-5996-4584-9586-2e750f3f772a
-- title:
--   Lemma 2.1 — Stein identity for the beta distribution
-- statement:
--   Let $b,m>0$, $n=b+m$, and $X\sim\mathrm{Beta}(b,m)$. Let $\phi:[0,1]\to\mathbb R$ be continuous on $[0,1]$ and locally absolutely continuous on $(0,1)$, with $\mathbb E\big[|X(1-X)\phi'(X)|\big]<\infty$. Then
--   $$\mathbb E\big[X(1-X)\phi'(X)\big]=\mathbb E\big[(nX-b)\phi(X)\big]=n\,\mathrm{Cov}\big[\phi(X),X\big].$$
--
--   This identity converts derivatives along a coordinate into covariances under the beta law; it underlies the count-deletion identity (Lemma 1.3) and the covariance bounds of the stability analysis.
--
--   Differences from the source:
--   - encoding: ϕ : [0,1] → ℝ, locally absolutely continuous on (0,1), ϕ′ → ϕ : ℝ → ℝ continuous on [0,1], absolutely continuous on every [c,d] with 0 < c ≤ d < 1, ϕ′ = deriv ϕ; reason: only values on [0,1] matter; local absolute continuity means absolute continuity on compact subintervals; deriv agrees with the a.e. derivative off a Beta-null set
--   - encoding: E[|X(1 − X)ϕ′(X)|] < ∞ → Integrable (x ↦ x(1−x)·deriv ϕ x) under Beta(b,m); reason: same condition
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Lemma 2.1, display (17), p.10

import Mathlib

open MeasureTheory ProbabilityTheory

namespace UCalibDirichlet

/-- **Lemma 2.1 (Stein identity for the beta distribution).** Frongillo, Luo, Mehta & Schneider,
*Near-Optimal Regret in U-Calibration for Every Proper Loss* (manuscript, STOC 2027 submission),
Lemma 2.1, display (17), p.10: "Let `b, m > 0` with `n = b + m`, and let `X ∼ Beta(b, m)`. If
`ϕ : [0, 1] → ℝ` is continuous on `[0, 1]` and locally absolutely continuous on `(0, 1)` with
`E[|X(1 − X)ϕ′(X)|] < ∞`, then `E[X(1 − X)ϕ′(X)] = E[(nX − b)ϕ(X)] = n Cov[ϕ(X), X]`. (17)"

**Formalization Note.** `ϕ : ℝ → ℝ`; only its values on `[0, 1]` matter. "Locally absolutely
continuous on `(0, 1)`" is absolute continuity on every compact interval `[c, d] ⊆ (0, 1)`; `ϕ′`
is `deriv ϕ` (it exists almost everywhere and the Beta law has a density). The moment condition
is `Integrable` with respect to `Beta(b, m)`; `Cov` is Mathlib's `covariance`. -/
theorem lemma_2_1 (b m : ℝ) (hb : 0 < b) (hm : 0 < m) (ϕ : ℝ → ℝ)
    (hcont : ContinuousOn ϕ (Set.Icc 0 1))
    (hac : ∀ c d : ℝ, 0 < c → c ≤ d → d < 1 → AbsolutelyContinuousOnInterval ϕ c d)
    (hint : Integrable (fun x => x * (1 - x) * deriv ϕ x) (betaMeasure b m)) :
    (∫ x, x * (1 - x) * deriv ϕ x ∂(betaMeasure b m)) =
        ∫ x, ((b + m) * x - b) * ϕ x ∂(betaMeasure b m) ∧
      (∫ x, ((b + m) * x - b) * ϕ x ∂(betaMeasure b m)) =
        (b + m) * covariance ϕ id (betaMeasure b m) := by sorry

end UCalibDirichlet
