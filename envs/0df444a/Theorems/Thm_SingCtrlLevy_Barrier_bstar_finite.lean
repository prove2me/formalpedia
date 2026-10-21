-- Prove2me | Theorems.Thm_SingCtrlLevy_Barrier_bstar_finite
-- name    : SingCtrlLevy.Barrier.bstar_finite
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:32.457412+00:00
-- url     : https://prove2.me/theorems/ae17aa84-1275-4383-b232-6907d36959b4
-- title:
--   §3 p. 6 (after (3.9)) — ρ is nondecreasing, ρ(±∞) = f′₊(±∞)/q, and −∞ < b* < ∞
-- statement:
--   Under Assumptions 1 and 2 and $q>0$, let $\rho(b)=\mathbb E\big[\int_0^\infty e^{-qt}f'_+(U^0_t+b)\,dt\big]$ as in (3.9). Then:
--
--   1. $b\mapsto\rho(b)$ is nondecreasing;
--   2. $\displaystyle\lim_{b\uparrow\infty}\rho(b)=\frac{f'_+(\infty)}{q}$ and $\displaystyle\lim_{b\downarrow-\infty}\rho(b)=\frac{f'_+(-\infty)}{q}$, with $f'_+(\pm\infty)=\lim_{y\to\pm\infty}f'_+(y)\in[-\infty,\infty]$;
--   3. the set $\{b\in\mathbb R:\rho(b)+C\ge0\}$ is nonempty and bounded below, so that
--   $$-\infty<b^*=\inf\{b\in\mathbb R:\rho(b)+C\ge0\}<\infty .$$
--
--   This is the statement that the barrier $b^*$ of (3.8) is a well-defined real number.
--
--   **Formalization Note** The limits are stated in the extended reals, with $f'_+(\infty)=\sup_y f'_+(y)$ and $f'_+(-\infty)=\inf_y f'_+(y)$ (equal to the limits since $f'_+$ is nondecreasing) multiplied by $1/q$. Finiteness of $b^*$ is stated as nonemptiness and boundedness below of the defining set, which is exactly what makes the infimum a real number. Assumption 2(i) is carried as a standing hypothesis.
-- source:
--   Noba & Yamazaki, On Singular Control for Lévy Processes, arXiv:2008.03021v3, p. 6, §3, paragraph after (3.9)

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_SingCtrlLevy_Barrier_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace SingCtrlLevy.Barrier

theorem bstar_finite {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (T : Triplet) (hX : IsLevyWith P X T)
    (f : ℝ → ℝ) (q C : ℝ) (hq : 0 < q) (hA1 : Assumption1 f C q) (hA2 : Assumption2ii T)
    (hA2i : ¬ T.DriftlessCP) :
    Monotone (rho P X f q) ∧
      Tendsto (fun b => (rho P X f q b : EReal)) atTop
        (𝓝 (((1 / q : ℝ) : EReal) * ⨆ y, (rd f y : EReal))) ∧
      Tendsto (fun b => (rho P X f q b : EReal)) atBot
        (𝓝 (((1 / q : ℝ) : EReal) * ⨅ y, (rd f y : EReal))) ∧
      {b : ℝ | 0 ≤ rho P X f q b + C}.Nonempty ∧
      BddBelow {b : ℝ | 0 ≤ rho P X f q b + C} := by sorry

end SingCtrlLevy.Barrier
