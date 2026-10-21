-- Prove2me | Theorems.Thm_SingCtrlLevy_Barrier_lemma_16
-- name    : SingCtrlLevy.Barrier.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:35.216588+00:00
-- url     : https://prove2.me/theorems/8aa11890-7f8f-4275-a330-2b626b38928a
-- title:
--   Lemma 16, p. 22 — for driftless compound Poisson X, ε ↦ b*_[ε] is nonincreasing and left-continuous at 0
-- statement:
--   Let $X$ be a driftless compound Poisson process ($\sigma=0$, $\Pi$ finite, $\Psi(u)=\int(1-e^{iuz})\Pi(dz)$) satisfying Assumption 2(ii), let $q>0$ and let Assumption 1 hold. For $\varepsilon\in\mathbb R$ let $X^{[\varepsilon]}_t=X_t+\varepsilon t$ and let $b^*_{[\varepsilon]}$ be the barrier (3.8) computed for $X^{[\varepsilon]}$. Then
--   $$\varepsilon\mapsto b^*_{[\varepsilon]}\ \text{is nonincreasing on }\mathbb R\ \text{and left-continuous at }0 .$$
--
--   This lemma lets §5 transfer Theorem 2 from the drifted processes $X^{[\varepsilon]}$, $\varepsilon\ne0$, to the driftless compound Poisson case $\varepsilon=0$.
--
--   **Formalization Note** Left continuity at $0$ is continuity within $(-\infty,0]$ at $0$. The hypothesis that $X$ is driftless compound Poisson replaces Assumption 2(i), as in §5.
-- source:
--   Noba & Yamazaki, On Singular Control for Lévy Processes, arXiv:2008.03021v3, p. 22, Lemma 16 (X^[ε], b*_[ε] defined p. 21)

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_SingCtrlLevy_Barrier_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace SingCtrlLevy.Barrier

theorem lemma_16 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (T : Triplet) (hX : IsLevyWith P X T)
    (f : ℝ → ℝ) (q C : ℝ) (hq : 0 < q) (hA1 : Assumption1 f C q) (hA2 : Assumption2ii T)
    (hDCP : T.DriftlessCP) :
    Antitone (fun ε => bstar P (XShift X ε) f q C) ∧
      ContinuousWithinAt (fun ε => bstar P (XShift X ε) f q C) (Set.Iic 0) 0 := by sorry

end SingCtrlLevy.Barrier
