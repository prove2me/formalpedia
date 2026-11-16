-- Prove2me | Theorems.Thm_QTolTest1673_Unified_Supplement_lemma_5_1
-- name    : QTolTest1673.Unified.Supplement.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:22:09.746121+00:00
-- url     : https://prove2.me/theorems/193ad059-0515-45f1-857c-87af903aff5d
-- title:
--   Lemma 5.1 — supports Theorem 1.2
-- statement:
--   Adding n−m irrelevant variables preserves distance to the Fourier-dimension-k class, dist(f̃, L_{n,k}) = dist(f, L_{m,k}) for k<m≤n, and one value query to f̃ is simulated by one value query to f.
--
--   $$\operatorname{dist}(\widetilde f,L_{n,k})=\operatorname{dist}(f,L_{m,k}).$$ Every algorithm on the extension has a simulator preserving its entire output law and its number of queries on every input, in both classical and quantum models.
--
--   This result supplies a supporting statement for Theorem 1.2, Theorem 1.4.
--
--   Differences from the source:
--   - encoding: sign-valued functions on one-based binary coordinates → bit-valued functions on Fin-indexed binary coordinates, with sign (-1)^bit; reason: the published models give a bijective representation and preserve the value oracle and uniform Hamming distance
--   - encoding: one value query to the extension is simulated by one query to f → every quantum or classical algorithm has a simulator preserving all output probabilities and query counts on each input; reason: composing the stated oracle simulation gives exactly this algorithm-level assertion; the first m coordinates are the original input
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, Lemma 5.1, p. 25

import Mathlib
import Definitions.Def_QTolTest1673_Unified_Supplement_Model

open scoped BigOperators
open Classical QAlgorithms FourierDimTesting102.Quantum
open Filter MeasureTheory

namespace QTolTest1673.Unified.Supplement

/-- Lemma 5.1, p.25: distance identity and exact one-for-one oracle simulation in both models. -/
theorem lemma_5_1 (k m n : ℕ) (hkm : k < m) (hmn : m ≤ n) :
  (∀ f : BoolFn m, distToSet (extendFn hmn f) (linJunta n k) =
    distToSet f (linJunta m k)) ∧
  (∀ A : AdaptiveQueryAlg (V n) Bool, ∃ B : AdaptiveQueryAlg (V m) Bool,
    ∀ f : BoolFn m, (∀ out, B.outProb f out = A.outProb (extendFn hmn f) out) ∧
      B.maxQueries f = A.maxQueries (extendFn hmn f)) ∧
  (∀ A : CAlg n, ∃ B : CAlg m, ∀ f : BoolFn m,
    (∀ out, B.outProb (answer f) out = A.outProb (answer (extendFn hmn f)) out) ∧
    (∀ q, B.MakesAtMost (answer f) q ↔ A.MakesAtMost (answer (extendFn hmn f)) q)) := by sorry

end QTolTest1673.Unified.Supplement
