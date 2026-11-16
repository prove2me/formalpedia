-- Prove2me | Theorems.Thm_QTolTest1673_Unified_Supplement_lemma_4_3
-- name    : QTolTest1673.Unified.Supplement.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:21:22.994512+00:00
-- url     : https://prove2.me/theorems/43a422df-a055-44ca-b141-a9489c4f4369
-- title:
--   Lemma 4.3 — Distance concentration
-- statement:
--   Distance concentration: for i.i.d. uniform signs f on F_2^n (n=k+s) and any finite family P of partitions into 2^k blocks of size L=2^s, Pr[min_P d_P(f) < e_s − τ] ≤ |P| exp(−8·2^k τ²) for every τ>0.
--
--   $$\Pr[\min_{P\in\mathcal P}\operatorname{dist}(f,\mathcal C_P)<e_s-\tau]\le |\mathcal P|e^{-8\cdot2^k\tau^2}.$$
--
--   This result supplies a supporting statement for Theorem 1.2, Theorem 6.1, Theorem 10.1.
--
--   Differences from the source:
--   - encoding: sign-valued functions on one-based binary coordinates → bit-valued functions on Fin-indexed binary coordinates, with sign (-1)^bit; reason: the published models give a bijective representation and preserve the value oracle and uniform Hamming distance
--   - encoding: the minimum partition distance is less than e_s−τ → there exists a member of a nonempty finite labelled partition family with distance less than e_s−τ; reason: minimum on the source family is defined only when it is nonempty; labelling changes neither blocks nor distance
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, Lemma 4.3, p. 23

import Mathlib
import Definitions.Def_QTolTest1673_Unified_Supplement_Partitions

open scoped BigOperators
open Classical QAlgorithms FourierDimTesting102.Quantum
open Filter MeasureTheory

namespace QTolTest1673.Unified.Supplement

/-- Lemma 4.3, p.23, with d_P defined as the actual minimum Hamming distance. -/
theorem lemma_4_3 (k s : ℕ) (hk : 1 ≤ k) (hs : 2 ≤ s)
    (F : Finset (Partition (k+s) (2^k))) (hF : F.Nonempty)
    (hblocks : ∀ P ∈ F, ∀ i : Fin (2^k),
      (Finset.univ.filter fun x => P x = i).card = 2^s)
    (τ : ℝ) (hτ : 0 < τ) :
  frac (fun f : BoolFn (k+s) => ∃ P ∈ F,
    distToSet f (partitionClass P) < blockMean s - τ) ≤
    F.card * Real.exp (-8*(2 : ℝ)^k*τ^2) := by sorry

end QTolTest1673.Unified.Supplement
