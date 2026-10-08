-- Prove2me | Theorems.Thm_TeschlQM_Herglotz_purely_ac_of_limsup_lt_top
-- name    : TeschlQM.Herglotz.purely_ac_of_limsup_lt_top
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:39:24.87546+00:00
-- url     : https://prove2.me/theorems/f61f2d77-915e-402f-8f51-da530ba9d313
-- title:
--   Corollary 3.24 — μ is purely absolutely continuous on I if limsup Im F(λ+iε) < ∞ on I
-- statement:
--   Let $\mu$ be a finite Borel measure on $\mathbb{R}$ with Borel transform $F$, and let $I \subseteq \mathbb{R}$ be a Borel set. If
--   $$\limsup_{\varepsilon\downarrow 0} \operatorname{Im} F(\lambda + i\varepsilon) < \infty \qquad \text{for all } \lambda \in I,$$
--   then $\mu$ is purely absolutely continuous on $I$: the restriction $\mu|_I$ is absolutely continuous with respect to Lebesgue measure.
--
--   **Formalization Note.** The book does not say what $I$ is (an interval in all its applications); any Borel set is allowed here, which includes intervals. The $\limsup$ is taken in `ℝ≥0∞` of the nonnegative quantities $\operatorname{Im} F(\lambda + i\varepsilon)$, $\varepsilon > 0$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 109, Corollary 3.24

import Mathlib
import Definitions.Def_TeschlQM_Herglotz_borelTransform

open MeasureTheory Filter
open scoped ENNReal Topology

namespace TeschlQM.Herglotz

/-- Teschl, p. 109, Corollary 3.24. Let `μ` be a finite Borel measure and `F` its Borel
transform. If `limsup_{ε↓0} Im(F(λ + iε)) < ∞` for all `λ` in a Borel set `I ⊆ ℝ`, then `μ` is
purely absolutely continuous on `I`: its restriction to `I` is absolutely continuous with
respect to Lebesgue measure. -/
theorem purely_ac_of_limsup_lt_top (μ : Measure ℝ) [IsFiniteMeasure μ] (I : Set ℝ)
    (hI : MeasurableSet I)
    (h : ∀ t ∈ I, limsup (fun ε : ℝ => ENNReal.ofReal
        (borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im) (𝓝[>] (0 : ℝ)) < ⊤) :
    μ.restrict I ≪ volume := by sorry

end TeschlQM.Herglotz
