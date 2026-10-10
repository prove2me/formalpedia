-- Prove2me | Theorems.Thm_RandomListsMatching_Concentration_lemma2_opt_upper_tail
-- name    : RandomListsMatching.Concentration.lemma2_opt_upper_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:07:43.298354+00:00
-- url     : https://prove2.me/theorems/252dcb1a-f3d1-428e-9298-2e27c2bebc06
-- title:
--   Lemma 2, p. 5 — P(OPT − E[OPT] > nε) ≤ exp(−2nε²)
-- statement:
--   Let $G = \{A \cup I, E\}$ be a bipartite graph with finitely many advertisers $A$, and let $n$ requests arrive with outcomes $\omega_1, \dots, \omega_n$ drawn i.i.d. from a probability law $\nu$ on a finite set $\mathcal X$, the $j$-th request having impression type $\mathrm{typ}(\omega_j) \in I$. Let $\mathrm{OPT}$ be the cardinality of a maximum matching of the realized graph, in which request $j$ may be assigned to advertiser $a$ iff $(a, \mathrm{typ}(\omega_j)) \in E$ and every advertiser receives at most one request. Then for every $\epsilon > 0$,
--   $$
--   \mathbb P\bigl(\mathrm{OPT} - \mathbb E[\mathrm{OPT}] > n\epsilon\bigr) \le \exp(-2n\epsilon^2).
--   $$
--
--   The offline optimum exceeds its mean by a linear amount only with exponentially small probability; together with Lemma 1 this gives the concluding display of Section 2.
--
--   **Formalization Note** The law of the arrivals is the product measure $\nu^{\otimes n}$ on $\mathcal X^n$, with the discrete σ-algebra. OPT depends on the outcomes only through the types. The inequality inside the probability is strict, as printed.
-- source:
--   Jaillet & Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (rev. June 2013), p. 5, Lemma 2

import Mathlib
import Definitions.Def_RandomListsMatching_Concentration_Setting

namespace RandomListsMatching.Concentration

open MeasureTheory

/-- **Lemma 2** (Jaillet & Lu, accepted manuscript (rev. June 2013), §2, p. 5).
`P(OPT − E[OPT] > nε) ≤ exp(−2nε²)` for `n` i.i.d. arrivals whose impression types are
`typ (ω j)`. -/
theorem lemma2_opt_upper_tail {A I X : Type} [Fintype A] (E : Finset (A × I)) [Fintype X]
    [MeasurableSpace X] [DiscreteMeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    (typ : X → I) (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (arrivalLaw ν n).real {ω | (OPT E typ ω : ℝ) - expOPT ν E typ n > (n : ℝ) * ε} ≤
      Real.exp (-2 * (n : ℝ) * ε ^ 2) := by sorry

end RandomListsMatching.Concentration
