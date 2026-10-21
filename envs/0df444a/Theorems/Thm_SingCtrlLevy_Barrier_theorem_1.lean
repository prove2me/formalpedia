-- Prove2me | Theorems.Thm_SingCtrlLevy_Barrier_theorem_1
-- name    : SingCtrlLevy.Barrier.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:22.598983+00:00
-- url     : https://prove2.me/theorems/00f9c36b-77c8-4a38-8408-061b5435410b
-- title:
--   Theorem 1, p. 8 — π^{b*} is optimal among barrier strategies: v_{b*}(x) ≤ v_b(x)
-- statement:
--   Under Assumptions 1 and 2 and $q>0$, the barrier strategy at $b^*=\inf\{b:\rho(b)+C\ge0\}$ is optimal over the set of barrier strategies $\mathcal A_{bar}=\{(R^b_t)_{t\ge0}:b\in\mathbb R\}$:
--   $$v_{b^*}(x)\le v_b(x)\qquad\text{for all }x,b\in\mathbb R .$$
--
--   It is the first half of the paper's argument; Theorem 2 extends the optimality to all admissible strategies.
--
--   **Formalization Note** Assumption 2(i) is carried as a standing hypothesis (§3).
-- source:
--   Noba & Yamazaki, On Singular Control for Lévy Processes, arXiv:2008.03021v3, p. 8, Theorem 1

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_SingCtrlLevy_Barrier_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace SingCtrlLevy.Barrier

theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (T : Triplet) (hX : IsLevyWith P X T)
    (f : ℝ → ℝ) (q C : ℝ) (hq : 0 < q) (hA1 : Assumption1 f C q) (hA2 : Assumption2ii T)
    (hA2i : ¬ T.DriftlessCP)
    (x b : ℝ) :
    vb P X f q C x (bstar P X f q C) ≤ vb P X f q C x b := by sorry

end SingCtrlLevy.Barrier
