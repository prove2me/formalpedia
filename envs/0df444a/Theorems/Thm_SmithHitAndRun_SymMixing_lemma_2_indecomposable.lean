-- Prove2me | Theorems.Thm_SmithHitAndRun_SymMixing_lemma_2_indecomposable
-- name    : SmithHitAndRun.SymMixing.lemma_2_indecomposable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:13:05.746983+00:00
-- url     : https://prove2.me/theorems/3b3c75d5-c64c-40b2-ad0a-cf2ad4fab592
-- title:
--   Lemma 2 — no two disjoint closed sets
-- statement:
--   Let $V$ be finite nonzero content on $S$ and $P$ a Markov kernel with a jointly measurable symmetric density $f(y\mid x)$ relative to $V$. Assume $f(y\mid x)>0$ for every $x,y\in S$. A set $A$ is closed when it is nonempty and measurable and $P(x,A)=1$ for every $x\in A$. Then
--   $$
--   \nexists A_1,A_2\subseteq S:\ A_1\cap A_2=\varnothing\ \text{and both }A_1,A_2\text{ are closed}.
--   $$
--   This is Smith's indecomposability condition. It supplies the one-step condition used in Theorems 1–2.
-- source:
--   Smith, Efficient Monte Carlo Procedures for Generating Points Uniformly Distributed over Bounded Regions, Oper. Res. 32(6) (1984), p. 1300, Lemma 2 and following definition of closed set

import Mathlib.Probability.Kernel.Invariance
import Definitions.Def_SmithHitAndRun_SymMixing_IsSymmetricMixingKernel
import Definitions.Def_SmithHitAndRun_SymMixing_IsClosedSet

open MeasureTheory ProbabilityTheory

namespace SmithHitAndRun.SymMixing

/-- Smith (1984), Lemma 2, p. 1300: no two disjoint nonempty closed sets. -/
theorem lemma_2_indecomposable {α : Type*} [MeasurableSpace α]
    (V : Measure α) [IsFiniteMeasure V] (hV : V ≠ 0)
    (P : Kernel α α) [IsMarkovKernel P] (f : α → α → ENNReal)
    (h : IsSymmetricMixingKernel V P f) (hpos : ∀ x y, 0 < f y x) :
    ¬ ∃ A₁ A₂ : Set α,
      IsClosedSet P A₁ ∧ IsClosedSet P A₂ ∧ A₁ ∩ A₂ = ∅ := by sorry

end SmithHitAndRun.SymMixing
