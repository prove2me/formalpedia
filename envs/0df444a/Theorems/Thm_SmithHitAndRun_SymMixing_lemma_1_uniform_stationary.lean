-- Prove2me | Theorems.Thm_SmithHitAndRun_SymMixing_lemma_1_uniform_stationary
-- name    : SmithHitAndRun.SymMixing.lemma_1_uniform_stationary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:13:01.287994+00:00
-- url     : https://prove2.me/theorems/611f54d5-7bb6-46f3-b723-4ae1bd9f24f8
-- title:
--   Lemma 1 — the uniform law is stationary
-- statement:
--   Let $V$ be finite nonzero content on $S$, let $P$ be a Markov kernel, and suppose $P$ has a jointly measurable symmetric density $f$ with respect to $V$ as in Assumption (a). Write $\lambda=V/V(S)$. For every measurable $A\subseteq S$,
--   $$
--   \lambda(A)=\int_S P(x,A)\,\lambda(dx).
--   $$
--   Thus a chain initially uniform on $S$ remains uniform after one transition. This is the stationary-law input for both main theorems. **Formalization Note** Assumption (b), strict positivity of $f$, is not required.
-- source:
--   Smith, Efficient Monte Carlo Procedures for Generating Points Uniformly Distributed over Bounded Regions, Oper. Res. 32(6) (1984), p. 1300, Lemma 1

import Mathlib.Probability.Kernel.Invariance
import Definitions.Def_SmithHitAndRun_SymMixing_uniformLaw
import Definitions.Def_SmithHitAndRun_SymMixing_IsSymmetricMixingKernel

open MeasureTheory ProbabilityTheory Filter

namespace SmithHitAndRun.SymMixing

/-- Smith (1984), Lemma 1, p. 1300: the uniform law is stationary. -/
theorem lemma_1_uniform_stationary {α : Type*} [MeasurableSpace α]
    (V : Measure α) [IsFiniteMeasure V] (hV : V ≠ 0)
    (P : Kernel α α) [IsMarkovKernel P] (f : α → α → ENNReal)
    (h : IsSymmetricMixingKernel V P f) :
    ∀ A : Set α, MeasurableSet A →
      uniformLaw V A = ∫⁻ x, P x A ∂(uniformLaw V) := by sorry

end SmithHitAndRun.SymMixing
