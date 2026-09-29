-- Prove2me | Theorems.Thm_SupportVectorMachines_Calibration_theorem_3_17_asymptotic_calibration_of_risks
-- name    : SupportVectorMachines.Calibration.theorem_3_17_asymptotic_calibration_of_risks
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T21:31:46.769222+00:00
-- url     : https://prove2.me/theorems/1c5daa33-6ae7-44d7-b20e-c7f9db5e7f51
-- title:
--   Theorem 3.17 — asymptotic calibration of risks
-- statement:
--   This is Theorem 3.17 (Asymptotic calibration of risks) of Steinwart & Christmann, *Support
--   Vector Machines* (Springer 2008, p. 60), this mission's main milestone toward Corollary 3.19:
--   the qualitative answer to "does making the surrogate risk small force the target risk small?"
--
--   Let $X$ be a complete measurable space, $L_{\mathrm{tar}}, L_{\mathrm{sur}}$ be losses, and
--   $P$ a distribution on $X \times Y$ with $R^*_{L_{\mathrm{tar}},P} < \infty$ and
--   $R^*_{L_{\mathrm{sur}},P} < \infty$. Then $x \mapsto \delta_{\max}(\varepsilon, P(\cdot\mid
--   x), x)$ is measurable for every $\varepsilon \in [0,\infty]$. Moreover, consider:
--
--   - **(i)** for all $\varepsilon \in (0,\infty]$, $P_X(\{x : \delta_{\max}(\varepsilon,
--     P(\cdot\mid x), x) = 0\}) = 0$;
--   - **(ii)** for all $\varepsilon \in (0,\infty]$, there is $\delta > 0$ such that, for every
--     measurable $f : X \to \mathbb R$, $R_{L_{\mathrm{sur}},P}(f) < R^*_{L_{\mathrm{sur}},P} +
--     \delta \implies R_{L_{\mathrm{tar}},P}(f) < R^*_{L_{\mathrm{tar}},P} + \varepsilon$
--     (Eq. (3.18)).
--
--   Then (ii) $\implies$ (i) always; and (i) $\implies$ (ii) holds whenever there is a
--   $P_X$-integrable $b : X \to [0,\infty)$ with $C_{L_{\mathrm{tar}},P(\cdot\mid x),x}(t) \le
--   C^*_{L_{\mathrm{tar}},P(\cdot\mid x),x} + b(x)$ for all $x, t$ (Eq. (3.19)).
--
--   **Formalization Note** $\varepsilon$ ranges over `ENNReal` throughout, so "$\varepsilon \in
--   [0,\infty]$"/"$(0,\infty]$" are rendered exactly (no narrowing to a finite range, unlike the
--   `Iic`-style real-valued conventions elsewhere in the series). `b`'s $P_X$-integrability is
--   `Integrable b PX` for a real-valued `b`, embedded into `ENNReal` via `ENNReal.ofReal` at the
--   single use site, matching "$b : X \to [0,\infty)$ $P_X$-integrable" without introducing a
--   separate `ENNReal`-valued integrability notion. `∀ x, IsProbabilityMeasure (κ x)` is again
--   added explicitly (see Lemma 3.4).
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 60, Theorem 3.17

import Mathlib
import Definitions.Def_SupportVectorMachines_Calibration_Loss
import Definitions.Def_SupportVectorMachines_Calibration_InnerRisks
import Definitions.Def_SupportVectorMachines_Calibration_OuterRisks
import Definitions.Def_SupportVectorMachines_Calibration_CalibrationFunction
import Definitions.Def_SupportVectorMachines_Calibration_IsCompleteMeasurableSpace

open MeasureTheory

namespace SupportVectorMachines.Calibration

/-- Theorem 3.17 (Asymptotic calibration of risks), p. 60: let `X` be a complete measurable
space, `Ltar, Lsur` be losses, and `P` (represented by `(PX, κ)`, `κ` a measurable family of
conditional distributions) be a distribution on `X × ℝ` with `R*_{Ltar,P} < ∞` and
`R*_{Lsur,P} < ∞`. Then `x ↦ δmax(ε, κ x, x)` is measurable for every `ε ∈ [0,∞]`. In addition:
ii) ⟹ i), where i) is "for all `ε ∈ (0,∞]`, `PX{x : δmax(ε,κ x,x) = 0} = 0`" and ii) is "for all
`ε ∈ (0,∞]` there is `δ > 0` such that, for all measurable `f`, `R_{Lsur,P}(f) < R*_{Lsur,P} + δ`
implies `R_{Ltar,P}(f) < R*_{Ltar,P} + ε`" (Eq. 3.18); and i) ⟹ ii) holds if there exists a
`PX`-integrable `b : X → [0,∞)` with `C_{Ltar,P(·|x),x}(t) ≤ C*_{Ltar,P(·|x),x} + b(x)` for all
`x, t` (Eq. 3.19). -/
theorem theorem_3_17_asymptotic_calibration_of_risks {X : Type*} [MeasurableSpace X]
    (hX : IsCompleteMeasurableSpace X) (Ltar Lsur : Loss X)
    (PX : Measure X) [IsProbabilityMeasure PX] (κ : X → Measure ℝ) (hκ : Measurable κ)
    (hκprob : ∀ x, IsProbabilityMeasure (κ x))
    (hLtar : bayesRisk Ltar PX κ < ⊤) (hLsur : bayesRisk Lsur PX κ < ⊤) :
    (∀ ε : ENNReal, Measurable (fun x => calibrationFunction Ltar Lsur (κ x) x ε)) ∧
    ((∀ ε : ENNReal, 0 < ε →
        ∃ δ : ENNReal, 0 < δ ∧ ∀ f : X → ℝ, Measurable f →
          outerRisk Lsur PX κ f < bayesRisk Lsur PX κ + δ →
          outerRisk Ltar PX κ f < bayesRisk Ltar PX κ + ε) →
      ∀ ε : ENNReal, 0 < ε →
        PX {x : X | calibrationFunction Ltar Lsur (κ x) x ε = 0} = 0) ∧
    ((∃ b : X → ℝ, (∀ x, 0 ≤ b x) ∧ Integrable b PX ∧
        ∀ x t, innerRisk Ltar (κ x) x t ≤ minInnerRisk Ltar (κ x) x + ENNReal.ofReal (b x)) →
      (∀ ε : ENNReal, 0 < ε →
          PX {x : X | calibrationFunction Ltar Lsur (κ x) x ε = 0} = 0) →
      ∀ ε : ENNReal, 0 < ε →
        ∃ δ : ENNReal, 0 < δ ∧ ∀ f : X → ℝ, Measurable f →
          outerRisk Lsur PX κ f < bayesRisk Lsur PX κ + δ →
          outerRisk Ltar PX κ f < bayesRisk Ltar PX κ + ε) := by sorry

end SupportVectorMachines.Calibration
