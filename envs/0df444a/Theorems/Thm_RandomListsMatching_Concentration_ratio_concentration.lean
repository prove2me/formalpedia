-- Prove2me | Theorems.Thm_RandomListsMatching_Concentration_ratio_concentration
-- name    : RandomListsMatching.Concentration.ratio_concentration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:07:59.877791+00:00
-- url     : https://prove2.me/theorems/98f788c9-9ee7-4dc1-a272-ec405ed5dcf4
-- title:
--   §2, p. 6 — P(ALG/OPT ≥ E[ALG]/E[OPT] − 2ε/(c+ε)) ≥ 1 − 2exp(−2nε²), c = E[OPT]/n, for every random-lists algorithm
-- statement:
--   Let $G = \{A \cup I, E\}$ be a bipartite graph with finitely many advertisers $A$. Let $n \ge 1$ requests arrive with outcomes $\omega_1, \dots, \omega_n$ drawn i.i.d. from a probability law $\nu$ on a finite set $\mathcal X$; the $j$-th request has impression type $\mathrm{typ}(\omega_j)$ and receives the list $\mathrm{lst}(\omega_j)$, and every list only contains advertisers interested in the type it comes with. Let $\mathrm{ALG}$ be the number of requests assigned by the list-greedy rule of the Random Lists Algorithms, and $\mathrm{OPT}$ the cardinality of a maximum matching of the realized graph. Put $c = \mathbb E[\mathrm{OPT}]/n$. Then for every $\epsilon > 0$,
--   $$
--   \mathbb P\left(\frac{\mathrm{ALG}}{\mathrm{OPT}} \ge \frac{\mathbb E[\mathrm{ALG}]}{\mathbb E[\mathrm{OPT}]} - \frac{2\epsilon}{c + \epsilon}\right) \ge 1 - 2\exp(-2n\epsilon^2).
--   $$
--
--   For every algorithm of the class, the competitive ratio in expectation, $\mathbb E[\mathrm{ALG}]/\mathbb E[\mathrm{OPT}]$, and the ratio $\mathrm{ALG}/\mathrm{OPT}$ achieved on most realizations are therefore close whenever $\mathbb E[\mathrm{OPT}]$ grows linearly in $n$.
--
--   **Formalization Note** The law of the arrivals is $\nu^{\otimes n}$ on $\mathcal X^n$ with the discrete σ-algebra; any joint law of type and list is allowed, which covers every Random Lists Algorithm. The hypothesis $n \ge 1$ is the paper's implicit "n requests" ($c = \mathbb E[\mathrm{OPT}]/n$). No hypothesis $\mathbb E[\mathrm{OPT}] > 0$ or $\mathrm{OPT} > 0$ is made; on realizations with $\mathrm{OPT} = 0$, and when $\mathbb E[\mathrm{OPT}] = 0$, Lean's convention $x/0 = 0$ applies, and the statement remains true under it.
-- source:
--   Jaillet & Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (rev. June 2013), p. 6, display after Lemma 2 (concluding §2)

import Mathlib
import Definitions.Def_RandomListsMatching_Concentration_Setting

namespace RandomListsMatching.Concentration

open MeasureTheory

/-- The display concluding §2 (Jaillet & Lu, accepted manuscript (rev. June 2013), p. 6): for every
Random Lists Algorithm, every `n ≥ 1` and every `ε > 0`,
`P(ALG/OPT ≥ E[ALG]/E[OPT] − 2ε/(c + ε)) ≥ 1 − 2 exp(−2nε²)`, where `c = E[OPT]/n`. -/
theorem ratio_concentration {A I X : Type} [DecidableEq A] [Fintype A] (E : Finset (A × I))
    [Fintype X] [MeasurableSpace X] [DiscreteMeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (typ : X → I) (lst : X → List A)
    (hint : ListsInterested E typ lst) (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) :
    1 - 2 * Real.exp (-2 * (n : ℝ) * ε ^ 2) ≤
      (arrivalLaw ν n).real
        {ω | expALG ν lst n / expOPT ν E typ n - 2 * ε / (expOPT ν E typ n / (n : ℝ) + ε) ≤
          (ALG lst ω : ℝ) / (OPT E typ ω : ℝ)} := by sorry

end RandomListsMatching.Concentration
