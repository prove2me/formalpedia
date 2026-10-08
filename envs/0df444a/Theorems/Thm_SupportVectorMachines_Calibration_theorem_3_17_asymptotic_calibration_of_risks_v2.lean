-- Prove2me | Theorems.Thm_SupportVectorMachines_Calibration_theorem_3_17_asymptotic_calibration_of_risks_v2
-- name    : SupportVectorMachines.Calibration.theorem_3_17_asymptotic_calibration_of_risks_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:43:23.380462+00:00
-- url     : https://prove2.me/theorems/3ca44a80-7c3c-435e-86ad-742624a60898
-- title:
--   Theorem 3.17 — asymptotic calibration of risks (measurable losses)
-- statement:
--   This is Theorem 3.17 (Asymptotic calibration of risks) of Steinwart & Christmann, *Support Vector Machines* (Springer 2008, p. 60).
--
--   Let $X$ be a complete measurable space, $L_{\mathrm{tar}}, L_{\mathrm{sur}}$ losses (Definition 2.1: measurable and nonnegative), and $P$ a distribution on $X \times Y$, represented by $(P_X,\kappa)$, with $R^*_{L_{\mathrm{tar}},P} < \infty$ and $R^*_{L_{\mathrm{sur}},P} < \infty$. Then $x \mapsto \delta_{\max}(\varepsilon, P(\cdot\mid x), x)$ is measurable for every $\varepsilon \in [0,\infty]$. Moreover, consider:
--
--   - **(i)** for all $\varepsilon \in (0,\infty]$, $P_X(\{x : \delta_{\max}(\varepsilon, P(\cdot\mid x), x) = 0\}) = 0$;
--   - **(ii)** for all $\varepsilon \in (0,\infty]$ there is $\delta > 0$ such that for every measurable $f : X \to \mathbb R$, $R_{L_{\mathrm{sur}},P}(f) < R^*_{L_{\mathrm{sur}},P} + \delta \implies R_{L_{\mathrm{tar}},P}(f) < R^*_{L_{\mathrm{tar}},P} + \varepsilon$ (Eq. (3.18)).
--
--   Then (ii) $\implies$ (i); and (i) $\implies$ (ii) whenever there is a $P_X$-integrable $b : X \to [0,\infty)$ with $C_{L_{\mathrm{tar}},P(\cdot\mid x),x}(t) \le C^*_{L_{\mathrm{tar}},P(\cdot\mid x),x} + b(x)$ for all $x,t$ (Eq. (3.19)).
--
--   **Formalization Note.** The retired version quantified over the bare function type for the losses, so a surrogate loss depending non-measurably on $x$ made the calibration function non-measurable and refuted the first conjunct. The corrected statement takes both losses in the bundled `Loss X` (measurable and nonnegative) and uses the book's definition of a complete measurable space. $\varepsilon, \delta$ range over `ENNReal`, so $[0,\infty]$ and $(0,\infty]$ are rendered exactly; $b$ is a real-valued nonnegative `Integrable` function embedded into $[0,\infty]$ at its use. Conventions made explicit (common to the corrected Chapter 3 milestones): a loss is the bundled `Loss X` of Definition 2.1 — measurable on $X \times \mathbb R \times \mathbb R$ and nonnegative — with the closed label set $Y$ embedded in $\mathbb R$ (a loss on $X \times Y \times \mathbb R$ extends by $0$ outside $Y$, a distribution on $X \times Y$ is one on $X \times \mathbb R$ supported on $X \times Y$, and a set $\mathcal Q$ of distributions on $Y$ is a set of measures on $\mathbb R$); a distribution $P$ on $X \times Y$ is represented by its marginal $P_X$ (a probability measure) together with a measurable family $\kappa : X \to \mathcal M(\mathbb R)$ of probability measures, the regular conditional probabilities $P(\cdot\mid x)$ (which exist since $Y$ is Polish, Lemma A.3.16; every statement is invariant under the choice of version), so that risks are written in the form of Eq. (3.5); all risks are $[0,\infty]$-valued Lebesgue integrals, as in the book; and `IsCompleteMeasurableSpace` is now the book's own notion (the $\sigma$-algebra equals its universal completion) instead of the retired stronger sufficient condition.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 60, Theorem 3.17

import Mathlib
import Definitions.Def_SupportVectorMachines_Calibration_Loss_v2
import Definitions.Def_SupportVectorMachines_Calibration_InnerRisks_v2
import Definitions.Def_SupportVectorMachines_Calibration_OuterRisks_v2
import Definitions.Def_SupportVectorMachines_Calibration_CalibrationFunction_v2
import Definitions.Def_SupportVectorMachines_Calibration_IsCompleteMeasurableSpace_v2

open MeasureTheory

namespace SupportVectorMachines.Calibration

/-- Theorem 3.17 (Asymptotic calibration of risks), Steinwart & Christmann, *Support Vector
Machines*, Springer 2008, p. 60: let `X` be a complete measurable space, `Ltar, Lsur` be losses
(Definition 2.1: measurable and nonnegative, bundled in `Loss X`), and `P` (represented by
`(PX, κ)`, `κ` a measurable family of conditional distributions) be a distribution on `X × ℝ`
with `R*_{Ltar,P} < ∞` and `R*_{Lsur,P} < ∞`. Then `x ↦ δmax(ε, κ x, x)` is measurable for every
`ε ∈ [0,∞]`. In addition: ii) ⟹ i), where i) is "for all `ε ∈ (0,∞]`,
`PX{x : δmax(ε,κ x,x) = 0} = 0`" and ii) is "for all `ε ∈ (0,∞]` there is `δ > 0` such that, for
all measurable `f`, `R_{Lsur,P}(f) < R*_{Lsur,P} + δ` implies `R_{Ltar,P}(f) < R*_{Ltar,P} + ε`"
(Eq. 3.18); and i) ⟹ ii) holds if there exists a `PX`-integrable `b : X → [0,∞)` with
`C_{Ltar,P(·|x),x}(t) ≤ C*_{Ltar,P(·|x),x} + b(x)` for all `x, t` (Eq. 3.19).
Corrected version of `theorem_3_17_asymptotic_calibration_of_risks`, whose `Loss X` was the bare
function type (no measurability, so the calibration function could fail to be measurable), and
whose completeness notion was a stronger sufficient condition. -/
theorem theorem_3_17_asymptotic_calibration_of_risks_v2 {X : Type*} [MeasurableSpace X]
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
