-- Prove2me | Theorems.Thm_UnderstandingML_pac_bayes_finite_class
-- name    : UnderstandingML.pac_bayes_finite_class
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T06:07:49.972475+00:00
-- url     : https://prove2.me/theorems/996132a0-a6ad-4038-8622-d0aed03d7e92
-- title:
--   Exercise 2: for finite H, uniform prior and point posteriors, w.p. ≥ 1−δ every h ∈ H has L_D(h) ≤ L_S(h) + √((ln|H| + ln(m/δ))/(2(m−1)))
-- statement:
--   **Exercise 2.** Suppose that $H$ is a finite hypothesis class, set the prior to be uniform over $H$, and set the posterior to be $Q(h_S) = 1$ for some $h_S$ and $Q(h) = 0$ for all other $h \in H$. Show that
--   $$L_D(h_S) \le L_S(h_S) + \sqrt{\frac{\ln(|H|) + \ln(m/\delta)}{2(m-1)}}.$$
--
--   Formally: with probability at least $1 - \delta$ over $S \sim D^m$, simultaneously for every $h \in H$; $m \ge 2$, $H$ nonempty, $[0,1]$-valued measurable loss.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §31.3 p. 418, Exercise 2 (first part)

import Definitions.Def_UnderstandingML_PACBayes

open MeasureTheory

namespace UnderstandingML

/-- **Exercise 2** (p. 418). Suppose that `H` is a finite hypothesis class, set the prior to be
uniform over `H`, and set the posterior to be `Q(h_S) = 1` for some `h_S` and `Q(h) = 0` for all
other `h ∈ H`. Then `L_D(h_S) ≤ L_S(h_S) + √((ln|H| + ln(m/δ)) / (2(m − 1)))`: with probability
at least `1 − δ`, simultaneously for every `h ∈ H`. `m ≥ 2`, `[0, 1]`-valued measurable loss. -/
theorem pac_bayes_finite_class {Z Hyp : Type*} [MeasurableSpace Z] (loss : Hyp → Z → ℝ)
    (H : Finset Hyp) (hH : H.Nonempty) (hmeas : ∀ h ∈ H, Measurable (loss h))
    (hloss : ∀ h z, loss h z ∈ Set.Icc (0 : ℝ) 1) (D : Measure Z) [IsProbabilityMeasure D]
    (m : ℕ) (hm : 2 ≤ m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    iidLaw D m {S | ∃ h ∈ H,
      empRisk loss S h + Real.sqrt ((Real.log H.card + Real.log (m / δ)) / (2 * (m - 1))) <
        risk loss D h} ≤ ENNReal.ofReal δ := by sorry

end UnderstandingML
