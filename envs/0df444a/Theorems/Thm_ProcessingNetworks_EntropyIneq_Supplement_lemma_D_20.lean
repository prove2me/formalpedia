-- Prove2me | Theorems.Thm_ProcessingNetworks_EntropyIneq_Supplement_lemma_D_20
-- name    : ProcessingNetworks.EntropyIneq.Supplement.lemma_D_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:09:22.31378+00:00
-- url     : https://prove2.me/theorems/ddbfe835-5d7d-563e-bad9-379f388f9157
-- title:
--   Lemma D.20 — every positive-step skeleton is irreducible and aperiodic
-- statement:
--   Let $X$ be an irreducible regular continuous-time Markov chain on a nonempty countable state space, and fix $h>0$. The **$h$-skeleton** is the discrete-time chain $Z_n=X(nh)$ with one-step transition kernel $P(h)$. Then $Z$ is irreducible and aperiodic.
--
--   Aperiodicity is stated by the equivalent return-time criterion: for every state $i$, there is an $N$ such that the $n$-step return probability to $i$ is positive for every $n\ge N$.
--
--   This lemma provides the discrete-time hypotheses used in the positive-recurrence and convergence arguments for skeleton chains.
--
--   **Formalization Note** The step is an element of $\mathbb R_{\ge0}$ with the strict hypothesis $h>0$. The kernel is the transition semigroup at $h$, not the embedded jump matrix and not a uniformized chain.
--
--   Differences from the source:
--   - encoding: the skeleton chain is aperiodic → at each state all sufficiently large return times have positive probability; reason: for an irreducible chain this is the standard period-one characterization and avoids a gcd of an infinite set
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Lemma D.20, p.294 (PDF 310)

import Mathlib
import Definitions.Def_ProcessingNetworks_EntropyIneq_Supplement_RegularCTMC

namespace ProcessingNetworks.EntropyIneq.Supplement

open MatrixAnalytic.ProductForm
open scoped NNReal

/-- **Lemma D.20.** Every strictly positive-step skeleton of an irreducible regular CTMC is an
irreducible and aperiodic discrete-time Markov chain.

Dai & Harrison, *Processing Networks* (pre-publication draft 2020-4-2, spnbook.org),
Lemma D.20, p.294 (PDF 310).

**Formalization Note** The `h`-skeleton has one-step kernel `P(h)`. Aperiodicity is expressed in
the standard irreducible-chain form: for every state, all sufficiently large return times have
positive probability. This is equivalent to period one and avoids taking a gcd of an infinite set.
The step size is explicitly positive; the zero-step identity kernel is excluded. -/
theorem lemma_D_20 {S : Type*} [Countable S] [DecidableEq S]
    (M : RegularCTMC S)
    (hirr : ProcessingNetworks.Stability.Irreducible
      (ProcessingNetworks.CTMCFoster.jumpPMF M.isGenerator))
    (h : ℝ≥0) (hh : 0 < h) :
    ProcessingNetworks.Stability.Irreducible (fun i => M.transition h i) ∧
      ∀ i : S, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        0 < ProcessingNetworks.Stability.stepIter (fun x => M.transition h x) n i i := by sorry

end ProcessingNetworks.EntropyIneq.Supplement
