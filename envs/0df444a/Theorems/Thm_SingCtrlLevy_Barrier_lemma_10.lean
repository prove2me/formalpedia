-- Prove2me | Theorems.Thm_SingCtrlLevy_Barrier_lemma_10
-- name    : SingCtrlLevy.Barrier.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:33.323645+00:00
-- url     : https://prove2.me/theorems/159359f0-7107-4fb6-a4c8-e74e82c23741
-- title:
--   Lemma 10, p. 15 — (L − q)v_{b*}(x) + f(x) = 0 for x ≥ b*
-- statement:
--   Under Assumptions 1, 2 and 3 and $q>0$, the candidate value function $v_{b^*}$ satisfies the equation
--   $$(\mathcal L-q)v_{b^*}(x)+f(x)=0\qquad\text{for all }x\in[b^*,\infty)\qquad(4.31).$$
--
--   Together with Lemma 11 and Lemma 8 this verifies the conditions of the verification lemma for $w=v_{b^*}$.
--
--   **Formalization Note** Assumption 3 is a hypothesis (it is vacuous when $X$ has bounded variation): §4.1 proves Theorem 2 under it. Assumption 2(i) is carried as a standing hypothesis.
-- source:
--   Noba & Yamazaki, On Singular Control for Lévy Processes, arXiv:2008.03021v3, p. 15, Lemma 10, (4.31)

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_SingCtrlLevy_Barrier_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace SingCtrlLevy.Barrier

theorem lemma_10 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (T : Triplet) (hX : IsLevyWith P X T)
    (f : ℝ → ℝ) (q C : ℝ) (hq : 0 < q) (hA1 : Assumption1 f C q) (hA2 : Assumption2ii T)
    (hA2i : ¬ T.DriftlessCP)
    (hA3 : Assumption3 T f) (x : ℝ) (hx : bstar P X f q C ≤ x) :
    gen T (fun y => vb P X f q C y (bstar P X f q C)) x
      - q * vb P X f q C x (bstar P X f q C) + f x = 0 := by sorry

end SingCtrlLevy.Barrier
