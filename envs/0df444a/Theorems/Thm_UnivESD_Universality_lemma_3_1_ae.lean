-- Prove2me | Theorems.Thm_UnivESD_Universality_lemma_3_1_ae
-- name    : UnivESD.Universality.lemma_3_1_ae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:18:25.288404+00:00
-- url     : https://prove2.me/theorems/18a3091e-0924-41fb-bc9a-e6979196959e
-- title:
--   Lemma 3.1 (dominated convergence, almost sure version)
-- statement:
--   Let $(X,\nu)$ be a finite measure space. For $n\ge1$ let $f_n:X\to\mathbb R$ be random functions which are jointly measurable with respect to $X$ and the underlying probability space $(\Omega,\mathbf P)$. Assume:
--
--   1. (uniform integrability) there exists $\delta>0$ such that $\int_X|f_n(x)|^{1+\delta}\,d\nu$ is almost surely bounded;
--   2. (pointwise convergence) for $\nu$-almost every $x\in X$, $f_n(x)$ converges almost surely to zero.
--
--   Then
--   $$\int_X f_n(x)\,d\nu(x)\longrightarrow0\quad\text{almost surely}.$$
--
--   This is the "resp." half of Lemma 3.1, used for the almost-sure replacement principle.
--
--   **Formalization Note.** The $(1+\delta)$-moment is the lower (extended-valued) integral, and "almost surely bounded" means $\mathbf P\bigl(\limsup_n\int^-|f_n|^{1+\delta}d\nu<\infty\bigr)=1$: with probability one there is $C$ bounding it for all large $n$. A Bochner integral would make hypothesis (i) vacuous for non-integrable $|f_n|^{1+\delta}$.
-- source:
--   Tao, Vu, Random matrices: Universality of ESDs and the circular law, Ann. Probab. 38 (2010), no. 5, p. 2036 (PDF 14), Lemma 3.1 (almost sure version)

import Mathlib
import Definitions.Def_UnivESD_Universality_Basic
import Definitions.Def_UnivESD_Universality_Model

open MeasureTheory Filter Topology

namespace UnivESD.Universality

/-- Lemma 3.1 (dominated convergence), almost sure convergence, p. 2036. -/
theorem lemma_3_1_ae {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → X → Ω → ℝ) (hf : ∀ n, Measurable (Function.uncurry (f n)))
    (h1 : ∃ δ : ℝ, 0 < δ ∧ ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      ∫⁻ x, ENNReal.ofReal (|f n x ω| ^ (1 + δ)) ∂ν ≤ ENNReal.ofReal C)
    (h2 : ∀ᵐ x ∂ν, ∀ᵐ ω ∂P, Tendsto (fun n => f n x ω) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, Tendsto (fun n => ∫ x, f n x ω ∂ν) atTop (𝓝 0) := by sorry

end UnivESD.Universality
