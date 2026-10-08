-- Prove2me | Theorems.Thm_TeschlQM_Herglotz_poisson_lower_of_ball_density
-- name    : TeschlQM.Herglotz.poisson_lower_of_ball_density
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T21:10:46.116738+00:00
-- url     : https://prove2.me/theorems/5438f547-71ad-4d06-ab62-61d24c67376f
-- title:
--   Local lower density bound for the Poisson integral
-- statement:
--   Let $\mu$ be a finite Borel measure on $\mathbb R$, $t\in\mathbb R$, $\delta>0$, and $c\ge0$. If every radius $0<r<\delta$ satisfies $\mu((t-r,t+r))/(2r)\ge c$, then for every $\varepsilon>0$,
--
--   $$\frac1\pi\operatorname{Im}F_\mu(t+i\varepsilon)\ge\frac{2c}{\pi}\arctan\frac\delta\varepsilon.$$
--
--   This is the quantitative lower estimate obtained by integrating the radial Poisson kernel against the symmetric-interval masses. No existence of a measure derivative is assumed.
-- source:
--   Auxiliary quantitative estimate extracted from G. Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99 (2009), pp. 108–109, proof of Theorem 3.22, Eq. (3.90). https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf (PDF pp. 119–120).

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Definitions.Def_TeschlQM_Herglotz_borelTransform

open MeasureTheory Filter Set
open scoped ENNReal Topology

theorem TeschlQM.Herglotz.poisson_lower_of_ball_density (μ : Measure ℝ) [IsFiniteMeasure μ]
    (t δ c ε : ℝ) (hδ : 0 < δ) (hc : 0 ≤ c) (hε : 0 < ε)
    (hdensity : ∀ r : ℝ, 0 < r → r < δ →
      ENNReal.ofReal c ≤ μ (Metric.ball t r) / volume (Metric.ball t r)) :
    c * (2 / Real.pi * Real.arctan (δ / ε)) ≤
      (TeschlQM.Herglotz.borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi := by sorry
