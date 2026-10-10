-- Prove2me | Theorems.Thm_RandomListsMatching_Concentration_lemma1_alg_lower_tail
-- name    : RandomListsMatching.Concentration.lemma1_alg_lower_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:07:43.52615+00:00
-- url     : https://prove2.me/theorems/c2156cdd-6a64-4d11-82e4-340e06b310ac
-- title:
--   Lemma 1, p. 5 — P(ALG − E[ALG] < −nε) ≤ exp(−2nε²)
-- statement:
--   Let $n$ requests arrive with outcomes $\omega_1, \dots, \omega_n$ drawn i.i.d. from a probability law $\nu$ on a finite set $\mathcal X$, the $j$-th request receiving the list $\mathrm{lst}(\omega_j)$ of advertisers, and let $\mathrm{ALG}$ be the number of requests assigned by the list-greedy rule (each request goes to the first unmatched advertiser of its list, or is dropped). Then for every $\epsilon > 0$,
--   $$
--   \mathbb P\bigl(\mathrm{ALG} - \mathbb E[\mathrm{ALG}] < -n\epsilon\bigr) \le \exp(-2n\epsilon^2).
--   $$
--
--   The online algorithm therefore falls far below its mean only with exponentially small probability; with Lemma 2 this links the ratio of expectations to the ratio on most realizations.
--
--   **Formalization Note** The law of the arrivals is the product measure $\nu^{\otimes n}$ on $\mathcal X^n$, with the discrete σ-algebra on the finite set $\mathcal X$. Types play no role here, and the lists are arbitrary. The inequality inside the probability is strict and the bound is a single exponential, as printed. At $n = 0$ the event is empty.
-- source:
--   Jaillet & Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (rev. June 2013), p. 5, Lemma 1

import Mathlib
import Definitions.Def_RandomListsMatching_Concentration_Setting

namespace RandomListsMatching.Concentration

open MeasureTheory

/-- **Lemma 1** (Jaillet & Lu, accepted manuscript (rev. June 2013), §2, p. 5).
`P(ALG − E[ALG] < −nε) ≤ exp(−2nε²)` for `n` i.i.d. arrivals, each carrying a list drawn
jointly with its type from a finite law `ν`. -/
theorem lemma1_alg_lower_tail {A X : Type} [DecidableEq A] [Fintype X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν] (lst : X → List A)
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (arrivalLaw ν n).real {ω | (ALG lst ω : ℝ) - expALG ν lst n < -((n : ℝ) * ε)} ≤
      Real.exp (-2 * (n : ℝ) * ε ^ 2) := by sorry

end RandomListsMatching.Concentration
