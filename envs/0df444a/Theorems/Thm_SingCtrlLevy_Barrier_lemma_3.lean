-- Prove2me | Theorems.Thm_SingCtrlLevy_Barrier_lemma_3
-- name    : SingCtrlLevy.Barrier.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:23.408363+00:00
-- url     : https://prove2.me/theorems/ff340dd0-98b9-4680-8a4b-eb14f064d40e
-- title:
--   Lemma 3, p. 6 — v_b(x) grows at most polynomially as x ↑ ∞
-- statement:
--   Under Assumptions 1 and 2 and $q>0$, fix a barrier $b\in\mathbb R$ and let $v_b(x)=v^{(1)}_b(x)+Cv^{(2)}_b(x)$ be the expected cost (3.6) of the barrier strategy at $b$ started from $x$. Then $v_b$ grows at most polynomially as $x\to\infty$: there are constants $k_1,k_2$ and $N\in\mathbb N$ such that
--   $$|v_b(x)|\le k_1+k_2|x|^N\qquad\text{for all sufficiently large }x .$$
--
--   For $x\le b$ the paper has the explicit linear form $v_b(x)=C(b-x)+v_b(b)$ (3.7); together with this lemma it gives polynomial growth of $v_b$ on the whole line.
--
--   **Formalization Note** "As $x\uparrow\infty$" is formalized as an eventual bound along `atTop`. Assumption 2(i) is carried as a standing hypothesis.
-- source:
--   Noba & Yamazaki, On Singular Control for Lévy Processes, arXiv:2008.03021v3, p. 6, Lemma 3

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_SingCtrlLevy_Barrier_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace SingCtrlLevy.Barrier

theorem lemma_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (T : Triplet) (hX : IsLevyWith P X T)
    (f : ℝ → ℝ) (q C : ℝ) (hq : 0 < q) (hA1 : Assumption1 f C q) (hA2 : Assumption2ii T)
    (hA2i : ¬ T.DriftlessCP)
    (b : ℝ) :
    ∃ k₁ k₂ : ℝ, ∃ N : ℕ, ∀ᶠ x in atTop, |vb P X f q C x b| ≤ k₁ + k₂ * |x| ^ N := by sorry

end SingCtrlLevy.Barrier
