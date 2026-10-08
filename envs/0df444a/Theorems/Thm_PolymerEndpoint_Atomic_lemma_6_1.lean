-- Prove2me | Theorems.Thm_PolymerEndpoint_Atomic_lemma_6_1
-- name    : PolymerEndpoint.Atomic.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:36:57.951985+00:00
-- url     : https://prove2.me/theorems/4a735639-f342-464b-8001-d36452270211
-- title:
--   Lemma 6.1 — semicontinuity of atom functionals
-- statement:
--   For each $\varepsilon\in(0,1)$, the mass-above-threshold functional is lower semicontinuous and measurable, while the indicator that the largest mass reaches $\varepsilon$ is upper semicontinuous and measurable:
--   $$
--   f\mapsto\|f\|_\varepsilon\ \text{is lower semicontinuous},\qquad
--   f\mapsto I_\varepsilon(f)\ \text{is upper semicontinuous}.
--   $$
--
--   These properties allow limiting laws to control atom mass even though the threshold functionals are not continuous.
-- source:
--   Bates and Chatterjee, The endpoint distribution of directed polymers, arXiv:1612.03443v5, p. 42, Lemma 6.1

import Definitions.Def_PolymerEndpoint_Atomic_Functionals

open MeasureTheory

namespace PolymerEndpoint.Atomic

theorem lemma_6_1 {d : ℕ} (hd : 1 ≤ d) (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    (LowerSemicontinuous (normEps (d := d) ε) ∧ Measurable (normEps (d := d) ε)) ∧
    (UpperSemicontinuous (Ieps (d := d) ε) ∧ Measurable (Ieps (d := d) ε)) := by sorry

end PolymerEndpoint.Atomic
