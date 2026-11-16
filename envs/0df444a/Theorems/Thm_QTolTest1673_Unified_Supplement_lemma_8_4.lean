-- Prove2me | Theorems.Thm_QTolTest1673_Unified_Supplement_lemma_8_4
-- name    : QTolTest1673.Unified.Supplement.lemma_8_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:28:20.135323+00:00
-- url     : https://prove2.me/theorems/b6e429ca-246b-4c0a-b29c-6b524585fffd
-- title:
--   Lemma 8.4 — Polynomial representation
-- statement:
--   Polynomial representation: the acceptance probability of any algorithm making q standard value queries to f (auxiliary registers, internal randomness, intermediate measurements allowed) is a real multilinear polynomial of degree at most 2q in the values f(x).
--
--   $$\Pr[A^f\text{ accepts}]=\sum_{S\subseteq X,\ |S|\le2q}c_S\prod_{x\in S}f(x).$$
--
--   This result supplies a supporting statement for Theorem 8.5.
--
--   Differences from the source:
--   - encoding: sign-valued Boolean oracle on a finite input set → the bit-valued oracle on the same input set, with sign (-1)^bit; reason: the change of encoding is bijective and uses the same standard XOR value oracle
--   - encoding: a real multilinear polynomial of degree at most 2q in signs → a real coefficient for each subset S, zero when |S|>2q, evaluating as the sum of coefficients times sign products; reason: subset monomials are precisely all squarefree monomials; a uniform maximum-query budget is the source q-query assumption
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, Lemma 8.4, p. 39

import Mathlib
import Definitions.Def_QTolTest1673_Unified_Supplement_Model

open scoped BigOperators
open Classical QAlgorithms FourierDimTesting102.Quantum
open Filter MeasureTheory

namespace QTolTest1673.Unified.Supplement

/-- Lemma 8.4, p.39: multilinear polynomial on signs, for general adaptive queries. -/
theorem lemma_8_4 {X : Type} [Fintype X] [DecidableEq X]
    (A : AdaptiveQueryAlg X Bool) (q : ℕ) (hq : ∀ f, A.maxQueries f ≤ q) :
  ∃ coefficients : Finset X → ℝ,
    (∀ S : Finset X, 2*q < S.card → coefficients S = 0) ∧
    ∀ f : X → Bool, A.outProb f true =
      ∑ S : Finset X, coefficients S * ∏ x ∈ S, if f x then (-1 : ℝ) else 1 := by sorry

end QTolTest1673.Unified.Supplement
