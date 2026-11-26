-- Prove2me | Theorems.Thm_SLLNCurves
-- name    : SLLNCurves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:58:00.908007+00:00
-- url     : https://prove2.me/theorems/86058a40-982f-5143-8a86-080cd49ed74b
-- title:
--   SLLNCurves: SLLNCurves
-- statement:
--   The Strong Law of Large Numbers step of Theorem 4.4 (paper.tex 1295-1310,
--   \eqref{countable_identity}, \eqref{stronglawlength}): given a Paolini–Stepanov family `F` for `T`
--   at a fixed stage `l` with `η_l(Θ(E)) ≠ 0`, and a countable family `om : ℕ → Form1 E` together with
--   any countable family `g : ℕ → Curve E → ℝ` of `η_l`-integrable functions, there is a single
--   sequence `γ : ℕ → Curve E` of curves of length exactly `l` (hence current-mass exactly `l`,
--   `\eqref{stronglawlength}`) realizing, simultaneously, the paper's `\eqref{countable_identity}`
--   current average (with the explicit `𝕄(T) = η_l(Θ(E))` factor of eq.~(4.6) carried through) at
--   `om`, and the generic strong-law average of `g` against the normalized measure
--   `η_l(Θ(E))⁻¹ • η_l`. This single node supplies every instance of the paper's countable
--   strong-law family at stage `l` that `BBSamplingDiagonal` needs, merging them into one
--   application of `SamplingRealizesAverages`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/SLLNCurves.lean#L22-L126
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/SLLNCurves.lean#L22-L126

import Definitions.Def_Tablet_SamplingRealizesAverages
import Definitions.Def_Tablet_PSFamily
import Definitions.Def_Tablet_CurveLenMeasurable
import Definitions.Def_Tablet_CurveCurrentMeasurable
import Definitions.Def_Tablet_CurveCurrentBound
import Definitions.Def_Tablet_ThetaL
import Definitions.Def_Tablet_SLLNCurves
import Theorems.Thm_CurveCurrentBound
import Theorems.Thm_CurveCurrentMeasurable
import Theorems.Thm_CurveLenMeasurable
import Theorems.Thm_SamplingRealizesAverages

set_option autoImplicit false
open MeasureTheory Filter Finset ENNReal

theorem SLLNCurves {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : Form1 E → ℝ) (F : PSFamily T) (l : ℕ) (hl : 1 ≤ l)
    (hne : F.eta l Set.univ ≠ 0)
    (om : ℕ → Form1 E)
    (g : ℕ → Curve E → ℝ) (hgm : ∀ j, Measurable (g j))
    (hgi : ∀ j, Integrable (g j) (F.eta l)) :
    ∃ γ : ℕ → Curve E,
      (∀ i, (γ i).len = (l : ℝ)) ∧
      (∀ i, massOfFunctional (curveCurrent (γ i)) = (l : ℝ≥0∞)) ∧
      (∀ k, Tendsto (fun n : ℕ =>
          (F.eta l Set.univ).toReal / (n * l) * ∑ i ∈ Finset.range n, curveCurrent (γ i) (om k))
          atTop (nhds (T (om k)))) ∧
      (∀ j, Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, g j (γ i)) / n) atTop
        (nhds ((F.eta l Set.univ).toReal⁻¹ * ∫ c, g j c ∂(F.eta l)))) := by sorry
