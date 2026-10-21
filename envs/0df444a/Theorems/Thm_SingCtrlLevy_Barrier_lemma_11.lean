-- Prove2me | Theorems.Thm_SingCtrlLevy_Barrier_lemma_11
-- name    : SingCtrlLevy.Barrier.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:23.512064+00:00
-- url     : https://prove2.me/theorems/8a074127-8b37-41d8-91b2-d03c3c476151
-- title:
--   Lemma 11, p. 15 — (L − q)v_{b*}(x) + f(x) ≥ 0 for x < b*
-- statement:
--   Under Assumptions 1, 2 and 3 and $q>0$, the candidate value function $v_{b^*}$ satisfies
--   $$(\mathcal L-q)v_{b^*}(x)+f(x)\ge0\qquad\text{for all }x<b^* .$$
--
--   With Lemma 10 it gives condition (4.29) of the verification lemma for $w=v_{b^*}$ on the whole line.
--
--   **Formalization Note** Assumption 3 is a hypothesis (vacuous under bounded variation), as in §4.1. Assumption 2(i) is carried as a standing hypothesis.
-- source:
--   Noba & Yamazaki, On Singular Control for Lévy Processes, arXiv:2008.03021v3, p. 15, Lemma 11

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_SingCtrlLevy_Barrier_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace SingCtrlLevy.Barrier

theorem lemma_11 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (T : Triplet) (hX : IsLevyWith P X T)
    (f : ℝ → ℝ) (q C : ℝ) (hq : 0 < q) (hA1 : Assumption1 f C q) (hA2 : Assumption2ii T)
    (hA2i : ¬ T.DriftlessCP)
    (hA3 : Assumption3 T f) (x : ℝ) (hx : x < bstar P X f q C) :
    0 ≤ gen T (fun y => vb P X f q C y (bstar P X f q C)) x
      - q * vb P X f q C x (bstar P X f q C) + f x := by sorry

end SingCtrlLevy.Barrier
