-- Prove2me | Theorems.Thm_QTolTest1673_Unified_Supplement_lemma_11_2
-- name    : QTolTest1673.Unified.Supplement.lemma_11_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:32:19.399195+00:00
-- url     : https://prove2.me/theorems/f7663037-6a8d-46b7-a058-60d4683946fe
-- title:
--   Lemma 11.2 — Marginals of the odd-parity distribution
-- statement:
--   Marginals of the odd-parity distribution: for L=2^s and v uniform among sign strings with product −1, every proper restriction v|_I is uniform on {±1}^I; in particular E ∏_{j∈I} v_j = 0 for ∅ ≠ I ⊊ [L].
--
--   $$\Pr[v|_I=w]=2^{-|I|}\quad(I\subsetneq[L]),\qquad\mathbb E\prod_{j\in I}v_j=0\quad(\varnothing\ne I\subsetneq[L]).$$
--
--   This result supplies a supporting statement for Theorem 11.4.
--
--   Differences from the source:
--   - encoding: sign-valued functions on one-based binary coordinates → bit-valued functions on Fin-indexed binary coordinates, with sign (-1)^bit; reason: the published models give a bijective representation and preserve the value oracle and uniform Hamming distance
--   - encoding: the restriction to every proper subset I is uniform → each assignment on I has probability 2^(−|I|) under the uniform odd-parity subtype; reason: these assignment probabilities exactly specify the entire marginal, including I empty
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, Lemma 11.2, p. 51

import Mathlib
import Definitions.Def_QTolTest1673_Unified_Supplement_Records

open scoped BigOperators
open Classical QAlgorithms FourierDimTesting102.Quantum
open Filter MeasureTheory

namespace QTolTest1673.Unified.Supplement

/-- Lemma 11.2, p.51: every proper marginal, including the empty marginal. -/
theorem lemma_11_2 (s : ℕ) (hs : 1 ≤ s) (I : Finset (Fin (2^s)))
    (hI : I ≠ Finset.univ) :
  (∀ a : I → Bool, oddAvg (2^s) (fun f => if (∀ i : I, f i = a i) then 1 else 0) =
    (2 : ℝ)^(-(I.card : ℤ))) ∧
  (I.Nonempty → oddAvg (2^s) (recordSign I) = 0) := by sorry

end QTolTest1673.Unified.Supplement
