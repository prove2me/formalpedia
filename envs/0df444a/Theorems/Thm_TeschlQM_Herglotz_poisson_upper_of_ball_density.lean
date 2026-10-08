-- Prove2me | Theorems.Thm_TeschlQM_Herglotz_poisson_upper_of_ball_density
-- name    : TeschlQM.Herglotz.poisson_upper_of_ball_density
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T21:10:51.434988+00:00
-- url     : https://prove2.me/theorems/685ac312-44ad-464f-9996-361edcb8d2fd
-- title:
--   Local upper density bound with a Poisson tail estimate
-- statement:
--   Let $\mu$ be a finite Borel measure on $\mathbb R$, $t\in\mathbb R$, $\delta>0$, and $c\ge0$. If every radius $0<r<\delta$ satisfies $\mu((t-r,t+r))/(2r)\le c$, then for every $\varepsilon>0$,
--
--   $$\frac1\pi\operatorname{Im}F_\mu(t+i\varepsilon)\le c+\frac{\varepsilon\mu(\mathbb R)}{\pi\delta^2}.$$
--
--   The local integral is at most $(2c/\pi)\arctan(\delta/\varepsilon)\le c$. Outside the interval of radius $\delta$, the kernel is at most $\varepsilon/\delta^2$. The remainder therefore vanishes as $\varepsilon\downarrow0$. No existence of a measure derivative is assumed.
-- source:
--   Auxiliary quantitative estimate extracted from G. Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99 (2009), pp. 108–109, proof of Theorem 3.22, Eq. (3.90). https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf (PDF pp. 119–120). The upper tail is weakened using ε/(δ²+ε²) ≤ ε/δ².

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Definitions.Def_TeschlQM_Herglotz_borelTransform

open MeasureTheory Filter Set
open scoped ENNReal Topology

theorem TeschlQM.Herglotz.poisson_upper_of_ball_density (μ : Measure ℝ) [IsFiniteMeasure μ]
    (t δ c ε : ℝ) (hδ : 0 < δ) (hc : 0 ≤ c) (hε : 0 < ε)
    (hdensity : ∀ r : ℝ, 0 < r → r < δ →
      μ (Metric.ball t r) / volume (Metric.ball t r) ≤ ENNReal.ofReal c) :
    (TeschlQM.Herglotz.borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi ≤
      c + (ε / δ ^ 2) * (μ Set.univ).toReal / Real.pi := by sorry
