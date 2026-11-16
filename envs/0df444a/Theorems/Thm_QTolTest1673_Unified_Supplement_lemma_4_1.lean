-- Prove2me | Theorems.Thm_QTolTest1673_Unified_Supplement_lemma_4_1
-- name    : QTolTest1673.Unified.Supplement.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:20:32.599121+00:00
-- url     : https://prove2.me/theorems/751034ec-e480-45d3-a910-e3481ac444da
-- title:
--   Lemma 4.1 — Hidden-partition collision bound
-- statement:
--   Hidden-partition collision bound: for any randomized adaptive classical algorithm with at most q queries, the TV distance between its transcripts under Y and N is at most the probability that two distinct points it queries under N fall in one block of the independently sampled partition.
--
--   $$d_{\mathrm{TV}}(\operatorname{tr}_Y,\operatorname{tr}_N)\le\Pr_{P,\operatorname{tr}_N}[\text{two distinct queried points are in one block}].$$
--
--   This result supplies a supporting statement for Theorem 1.2, Theorem 6.1.
--
--   Differences from the source:
--   - encoding: sign-valued functions on one-based binary coordinates → bit-valued functions on Fin-indexed binary coordinates, with sign (-1)^bit; reason: the published models give a bijective representation and preserve the value oracle and uniform Hamming distance
--   - generalization: hidden partitions into equal-sized blocks → arbitrary labelled partitions, including unequal blocks; reason: the coupling until the first collision uses no block-size assumption; every source partition is included
--   - encoding: a random hidden parameter and its partition → a PMF on labelled partitions; complete traces include the final halt/output; reason: the finite input has finitely many partitions, so pushforward of any hidden law has this representation; the behaviour strategy records its random action draws
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, Lemma 4.1, p. 21

import Mathlib
import Definitions.Def_QTolTest1673_Unified_Supplement_Partitions

open scoped BigOperators
open Classical QAlgorithms FourierDimTesting102.Quantum
open Filter MeasureTheory

namespace QTolTest1673.Unified.Supplement

/-- Lemma 4.1, p.21. Arbitrary hidden laws on labelled partitions; equal sizes are unnecessary. -/
theorem lemma_4_1 {n b : ℕ} (law : PMF (Partition n b))
    (A : CAlg n) (q : ℕ)
    (hbound : ∀ f, A.MakesAtMost (answer f) q) :
  traceTV A (yesOracle law) (PMF.uniformOfFintype (BoolFn n)) q ≤
    collisionProb A law q := by sorry

end QTolTest1673.Unified.Supplement
