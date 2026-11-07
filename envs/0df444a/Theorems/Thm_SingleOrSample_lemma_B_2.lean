-- Prove2me | Theorems.Thm_SingleOrSample_lemma_B_2
-- name    : SingleOrSample.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:49:02.321799+00:00
-- url     : https://prove2.me/theorems/7c56fe1b-48e2-4ce6-a83f-817bef4f3b84
-- title:
--   Lemma B.2 — adaptive bucketing
-- statement:
--   Let $A$ be drawn from a finite set $G$ through a multi-bucket SwR process with probability bound $p$, where the buckets and their probabilities may be chosen adaptively from the history of the process. For every fixed $T\subseteq G$,
--   $$\Pr[T\subseteq A]\le p^{|T|}.$$
--   Adaptivity destroys negative association of the selection events (Appendix D of the paper), yet this bound of an independent Bernoulli process survives.
--
--   Differences from the source: none.
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Lemma B.2, p.31

import Mathlib
import Definitions.Def_SingleOrSample_multiBucketLaw

namespace SingleOrSample

/-- **Lemma B.2, adaptive bucketing** (Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Lemma B.2, p.31). In a multi-bucket SwR process on `G` with
probability bound `p`, with buckets and probabilities chosen adaptively from the history, every fixed
`T ⊆ G` has `Pr[T ⊆ A] ≤ p^|T|`. -/
theorem lemma_B_2 {α : Type*} (G : Finset α) (p : unitInterval)
    (rule : List (Finset α × unitInterval × Finset α) → Finset α × unitInterval)
    (hrule : IsMultiBucketRule G p rule) (T : Finset α) (hT : T ⊆ G) :
    (multiBucketLaw G rule).toOuterMeasure {l | T ⊆ sampledSet l} ≤
      ENNReal.ofReal ((p : ℝ) ^ T.card) := by sorry

end SingleOrSample
