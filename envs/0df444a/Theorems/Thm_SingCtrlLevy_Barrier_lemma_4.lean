-- Prove2me | Theorems.Thm_SingCtrlLevy_Barrier_lemma_4
-- name    : SingCtrlLevy.Barrier.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:14.65592+00:00
-- url     : https://prove2.me/theorems/6f3e05cd-07f7-4f5b-9ed7-a0123399ec37
-- title:
--   Lemma 4, p. 6 — E_x[∫₀^∞ e^{−qt}|f′₊(U^b_t)| dt] < ∞
-- statement:
--   Under Assumptions 1 and 2 and $q>0$, for every starting point $x\in\mathbb R$ and barrier $b\in\mathbb R$, the right derivative of the running cost along the reflected process is discounted-integrable:
--   $$\mathbb E_x\Big[\int_0^\infty e^{-qt}\,\big|f'_+(U^b_t)\big|\,dt\Big]<\infty ,$$
--   where $U^b=x+X+R^b$ is $X$ started at $x$ and reflected at the lower barrier $b$.
--
--   This makes $\rho(b)$ in (3.9) a genuine (finite) expectation.
--
--   **Formalization Note** The left side is a lower Lebesgue integral in $[0,\infty]$; the claim is that it is finite. Assumption 2(i) is carried as a standing hypothesis.
-- source:
--   Noba & Yamazaki, On Singular Control for Lévy Processes, arXiv:2008.03021v3, p. 6, Lemma 4

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_SingCtrlLevy_Barrier_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace SingCtrlLevy.Barrier

theorem lemma_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (T : Triplet) (hX : IsLevyWith P X T)
    (f : ℝ → ℝ) (q C : ℝ) (hq : 0 < q) (hA1 : Assumption1 f C q) (hA2 : Assumption2ii T)
    (hA2i : ¬ T.DriftlessCP)
    (x b : ℝ) :
    ∫⁻ ω, (∫⁻ t in Set.Ici (0 : ℝ),
      ENNReal.ofReal (Real.exp (-q * t) * |rd f (U X x (barrierR X x b) t.toNNReal ω)|)) ∂P
      < ⊤ := by sorry

end SingCtrlLevy.Barrier
