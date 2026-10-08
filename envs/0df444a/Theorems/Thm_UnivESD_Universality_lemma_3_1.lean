-- Prove2me | Theorems.Thm_UnivESD_Universality_lemma_3_1
-- name    : UnivESD.Universality.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:18:31.47455+00:00
-- url     : https://prove2.me/theorems/bb7b7767-74c1-4436-9a0c-900b93a17581
-- title:
--   Lemma 3.1 (dominated convergence, in probability)
-- statement:
--   Let $(X,\nu)$ be a finite measure space. For $n\ge1$ let $f_n:X\to\mathbb R$ be random functions which are jointly measurable with respect to $X$ and the underlying probability space $(\Omega,\mathbf P)$. Assume:
--
--   1. (uniform integrability) there exists $\delta>0$ such that $\int_X|f_n(x)|^{1+\delta}\,d\nu$ is bounded in probability;
--   2. (pointwise convergence in probability) for $\nu$-almost every $x\in X$, $f_n(x)$ converges in probability to zero.
--
--   Then
--   $$\int_X f_n(x)\,d\nu(x)\longrightarrow0\quad\text{in probability}.$$
--
--   This is the probabilistic dominated convergence theorem that drives the proof of the replacement principle.
--
--   **Formalization Note.** The $(1+\delta)$-moment is the lower (extended-valued) integral $\int^-|f_n|^{1+\delta}\,d\nu\in[0,\infty]$, and "bounded in probability" means: for every $\varepsilon>0$ there is $C$ with $\mathbf P\bigl(\int^-|f_n|^{1+\delta}d\nu>C\bigr)\le\varepsilon$ for all large $n$. A Bochner integral would be $0$ for a non-integrable $|f_n|^{1+\delta}$ and make hypothesis (i) vacuous for such $f_n$. Joint measurability is measurability of $(x,\omega)\mapsto f_n(x,\omega)$ for the product $\sigma$-algebra.
-- source:
--   Tao, Vu, Random matrices: Universality of ESDs and the circular law, Ann. Probab. 38 (2010), no. 5, p. 2036 (PDF 14), Lemma 3.1 (convergence in probability version)

import Mathlib
import Definitions.Def_UnivESD_Universality_Basic
import Definitions.Def_UnivESD_Universality_Model

open MeasureTheory Filter Topology

namespace UnivESD.Universality

/-- Lemma 3.1 (dominated convergence), convergence in probability, p. 2036. -/
theorem lemma_3_1 {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → X → Ω → ℝ) (hf : ∀ n, Measurable (Function.uncurry (f n)))
    (h1 : ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      P {ω | ENNReal.ofReal C < ∫⁻ x, ENNReal.ofReal (|f n x ω| ^ (1 + δ)) ∂ν}
        ≤ ENNReal.ofReal ε)
    (h2 : ∀ᵐ x ∂ν, TendstoInProbZero P fun n ω => f n x ω) :
    TendstoInProbZero P fun n ω => ∫ x, f n x ω ∂ν := by sorry

end UnivESD.Universality
