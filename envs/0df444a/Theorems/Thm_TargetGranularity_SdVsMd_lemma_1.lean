-- Prove2me | Theorems.Thm_TargetGranularity_SdVsMd_lemma_1
-- name    : TargetGranularity.SdVsMd.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:32.657499+00:00
-- url     : https://prove2.me/theorems/37932880-b31d-4571-b070-9221de55e4dd
-- title:
--   Lemma 1, p. 13 (PDF 14), first sentence — under sd targeting the click set is [0,1] minus an interval
-- statement:
--   Consider the single-dimensional environment with price $p\in(0,1)$ and click cost $c_{click}>0$. Let $\widetilde\Sigma\subseteq[0,1]$ be a measurable expected targeting set of positive length, and let $\Omega^{sd}(\widetilde\Sigma)$ be the set of weights $\omega\in[0,1]$ whose posterior expected surplus $E[\max\{u-p,0\};\widetilde\Sigma]$ is at least $c_{click}$. Then there are real numbers $\underline\omega\le\overline\omega$ such that
--   $$\Omega^{sd}(\widetilde\Sigma)=\{\omega\in[0,1]:\ \omega\le\underline\omega\ \text{or}\ \omega\ge\overline\omega\}.$$
--
--   Consumers with extreme weights click and consumers with intermediate weights do not. This is the shape of the click decision that the analysis of the sd equilibrium builds on.
--
--   **Formalization Note** The thresholds are arbitrary reals, so the statement covers the empty click set and click sets $[\overline\omega,1]$ without $0$; the page's form $[0,\underline\omega]\cup[\overline\omega,1]$ with $0\le\underline\omega\le\overline\omega\le1$ always contains $0$ and $1$ and cannot express those cases. The remaining sentences of Lemma 1 are not formalized.
-- source:
--   Despotakis & Yu, Multidimensional Targeting and Consumer Response, SSRN 3900394 (version of October 11, 2022), p. 13 (PDF 14), Lemma 1 (first sentence)

import Mathlib
import Definitions.Def_TargetGranularity_SdVsMd_Model

namespace TargetGranularity.SdVsMd

/-- Lemma 1, p. 13 (first sentence): under sd targeting, for every non-null measurable expected
targeting set `Σ̃ ⊆ [0,1]`, the click set is `[0,1]` minus an interval, i.e.
`{ω ∈ [0,1] | ω ≤ ω̲ ∨ ω̄ ≤ ω}` for some reals `ω̲ ≤ ω̄`. -/
theorem lemma_1 (p cclick : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hcclick : 0 < cclick)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ Set.Icc 0 1)
    (hSpos : 0 < MeasureTheory.volume S) :
    ∃ ωlo ωhi : ℝ, ωlo ≤ ωhi ∧
      sdClick p cclick S = {ω ∈ Set.Icc (0 : ℝ) 1 | ω ≤ ωlo ∨ ωhi ≤ ω} := by sorry

end TargetGranularity.SdVsMd
