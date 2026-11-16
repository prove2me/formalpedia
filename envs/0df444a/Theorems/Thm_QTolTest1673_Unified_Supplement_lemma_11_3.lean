-- Prove2me | Theorems.Thm_QTolTest1673_Unified_Supplement_lemma_11_3
-- name    : QTolTest1673.Unified.Supplement.lemma_11_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:33:17.593562+00:00
-- url     : https://prove2.me/theorems/d46d912a-06a4-4c4c-baad-e4d7b51ed830
-- title:
--   Lemma 11.3 — Hamming-ball bound
-- statement:
--   Hamming-ball bound: for s=2t ≤ n, a fixed A ⊆ F_2^n and a uniform s-subset U of [n], Pr_U[some U-subcube contains at least 2^{s−1} points of A] ≤ C(|A|,2)(s/n)^t.
--
--   $$\Pr_U[\exists\text{ a }U\text{-subcube containing at least }2^{2t-1}\text{ points of }A]\le\binom{|A|}{2}(2t/n)^t.$$
--
--   This result supplies a supporting statement for Theorem 11.4.
--
--   Differences from the source:
--   - encoding: sign-valued functions on one-based binary coordinates → bit-valued functions on Fin-indexed binary coordinates, with sign (-1)^bit; reason: the published models give a bijective representation and preserve the value oracle and uniform Hamming distance
--   - encoding: a uniform s-subset, s=2t, and some U-subcube → a uniform subtype of coordinate sets of cardinality 2t, and the subcube through some input; reason: all and only source coordinate sets and subcubes are represented; the ratio power is written (2t)^t/n^t
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, Lemma 11.3, p. 52

import Mathlib
import Definitions.Def_QTolTest1673_Unified_Supplement_Records

open scoped BigOperators
open Classical QAlgorithms FourierDimTesting102.Quantum
open Filter MeasureTheory

namespace QTolTest1673.Unified.Supplement

/-- Lemma 11.3, p.52: all point sets, including ∅ and singletons. -/
theorem lemma_11_3 (n t : ℕ) (hn : 0 < n) (ht : 0 < t) (hs : 2*t ≤ n)
    (A : Finset (V n)) :
  letI : Fintype (CoordSets n (2*t)) := Fintype.ofFinite _
  frac (fun U : CoordSets n (2*t) =>
    ∃ x : V n, 2^(2*t-1) ≤ (A ∩ subcube U.val x).card) ≤
      (Nat.choose A.card 2 : ℝ) * ((2*t : ℕ) : ℝ)^t / (n : ℝ)^t := by sorry

end QTolTest1673.Unified.Supplement
