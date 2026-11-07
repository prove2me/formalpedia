-- Prove2me | Theorems.Thm_ReplicableDecisions_lemma_3_5
-- name    : ReplicableDecisions.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:05:54.802191+00:00
-- url     : https://prove2.me/theorems/8c90a977-bee7-4fca-94fb-a0071ff6bac1
-- title:
--   Lemma 3.5 — maximum-likelihood tail: $\Pr[h(P,\widehat P(S))\ge r]\le(M-1)e^{-nr^2}$
-- statement:
--   Let $\widehat P(S)$ be a maximum-likelihood model in $\mathcal P$. For every $P\in\mathcal P$, $n\ge1$ and $r>0$,
--
--   $$
--   \Pr_{S\sim P^n}\bigl[h(P,\widehat P(S))\ge r\bigr]\le(M-1)e^{-nr^2}.
--   $$
--
--   The bound is the statistical input of the upper bound, and it depends on the experiment only through $M$.
--
--   Differences from the source:
--   - encoding: a known family P = {P1, …, PM} of distinct distributions on a finite set Z → an `Experiment ι Z`: an injective table of probability vectors over a finite index type, with Z in `Type` and M = `Fintype.card ι`; reason: models are named by index; the reused Bhattacharyya coefficient takes a type in `Type`, which loses no finite Z
--   - encoding: probabilities over S, S′ ∼ Pⁿ and the seed R → finite sums over samples `Fin n → Z` of products of table entries times seed-measure terms `μ.real`; reason: the data side is finite; the same numbers
--   - generalization: a maximum-likelihood model with fixed tie-breaking → any function `mle` of the sample selecting a likelihood maximizer; reason: the proof bounds the event pointwise in the sample and never uses how ties are broken; every fixed tie-breaking is such a function
-- source:
--   Chen, Replicable Decisions in Finite Experiments, STOC 2027 submission (sha256 52d181db…), Lemma 3.5, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_ReplicableDecisions_hellinger
import Definitions.Def_ReplicableDecisions_IsMaxLikelihood

namespace ReplicableDecisions

/-- **Lemma 3.5 (Finite-model estimation).** Chen, *Replicable Decisions in Finite Experiments*, STOC
2027 submission (sha256 52d181db…), Lemma 3.5, p.13 (PDF p.15): for a maximum-likelihood model `P̂(S)`,
every `P`, `n ≥ 1` and `r > 0`, `Pr_{S∼Pⁿ}[h(P, P̂(S)) ≥ r] ≤ (M − 1)e^{−nr²}`.

**Formalization Note.** `M − 1` is a real subtraction. The bound holds for every selection of a
likelihood maximizer, which covers every fixed tie-breaking. -/
theorem lemma_3_5 {ι : Type*} {Z : Type} [Fintype ι] [Fintype Z] (E : Experiment ι Z) {n : ℕ}
    (mle : (Fin n → Z) → ι) (hmle : IsMaxLikelihood E mle) (i : ι) (hn : 1 ≤ n) {r : ℝ}
    (hr : 0 < r) :
    finProb (productLaw (E.P i) (n := n)) {x | r ≤ hellinger (E.P i) (E.P (mle x))} ≤
      ((Fintype.card ι : ℝ) - 1) * Real.exp (-(n : ℝ) * r ^ 2) := by sorry

end ReplicableDecisions
