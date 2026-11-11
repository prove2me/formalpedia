-- Prove2me | Theorems.Thm_QuantumCycleColoring_FourColor_lemma_6_2
-- name    : QuantumCycleColoring.FourColor.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:00:06.406996+00:00
-- url     : https://prove2.me/theorems/1d9e4dc7-7446-4282-a9c2-b9c251ce4117
-- title:
--   Lemma 6.2: two-point bound for stationary 1-dependent $\{0,1\}$ processes
-- statement:
--   Let $(Y_t)_{t\in\mathbb Z}$ be a stationary $1$-dependent process with values in $\{0,1\}$ on a probability space. If
--   $$\alpha:=\Pr[Y_t=1]\in[\tfrac14,\tfrac13],$$
--   then
--   $$\Pr[Y_t=1,\ Y_{t+1}=1]\ \ge\ \frac{\big(1-2\sqrt{1-3\alpha}\big)\big(1+\sqrt{1-3\alpha}\big)^2}{27}.$$
--
--   This classical bound on 1-dependent processes is what converts a mass slightly above $1/4$ into a definite amount of energy (Lemma 6.3).
--
--   Differences from the source:
--   - encoding: a stationary 1-dependent process (Y_t ∈ {0,1})_{t∈ℤ} and the probability Pr → measurable Y : ℤ → Ω → Fin 2 on a probability space (Ω, μ), satisfying IsStationaryProcess μ Y and IsKDependent 1 μ Y; probabilities are μ.real of events; reason: the same processes and probabilities
--   - encoding: α := Pr[Y_t = 1] (independent of t by stationarity) → the hypotheses and the conclusion are stated for an arbitrary fixed t with α written out as μ.real {Y t = 1}; reason: the paper's statement is for every t
-- source:
--   Tom Gur, Longcheng Li, STOC 2027 submission #515 (October 2026), Lemma 6.2, p.42 (cited from Gandolfi–Keane–de Valk 1989, Section 2)

import Mathlib
import Definitions.Def_QuantumCycleColoring_FourColor_DependentProcess

namespace QuantumCycleColoring.FourColor

open MeasureTheory ProbabilityTheory

/-- Lemma 6.2, p.42 (Gur–Li, STOC 2027 #515; Section 2 of Gandolfi–Keane–de Valk 1989). For a
stationary 1-dependent process `(Y_t ∈ {0,1})_{t∈ℤ}` on a probability space, if
`α = Pr[Y_t = 1] ∈ [1/4, 1/3]` then
`Pr[Y_t = 1, Y_{t+1} = 1] ≥ (1 − 2√(1 − 3α))(1 + √(1 − 3α))² / 27`. -/
theorem lemma_6_2 {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℤ → Ω → Fin 2) (hstat : IsStationaryProcess μ Y) (hdep : IsKDependent 1 μ Y)
    (t : ℤ) (hα1 : 1 / 4 ≤ μ.real {ω | Y t ω = 1}) (hα2 : μ.real {ω | Y t ω = 1} ≤ 1 / 3) :
    (1 - 2 * Real.sqrt (1 - 3 * μ.real {ω | Y t ω = 1})) *
        (1 + Real.sqrt (1 - 3 * μ.real {ω | Y t ω = 1})) ^ 2 / 27 ≤
      μ.real {ω | Y t ω = 1 ∧ Y (t + 1) ω = 1} := by sorry

end QuantumCycleColoring.FourColor
