-- Prove2me | Theorems.Thm_QTolTest1673_Unified_Supplement_lemma_9_2
-- name    : QTolTest1673.Unified.Supplement.lemma_9_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:30:50.792661+00:00
-- url     : https://prove2.me/theorems/36735b49-1026-4f2d-85e8-4bdacd767820
-- title:
--   Lemma 9.2 — Comparison using good records
-- statement:
--   Comparison using good records: if the good-record families G_u ∋ ∅ give orthonormal record vectors under D_u and ρ_t bounds (23) for t<q, every q-query algorithm whose initial state and inter-query operations are independent of u has |E_u E_{f∼D_u} Pr[accept|f] − E_{f∼D_0} Pr[accept|f]| ≤ 4 Σ_{t<q} √ρ_t.
--
--   $$\left|\mathbb E_u\mathbb E_{f\sim D_u}\Pr[A^f\text{ accepts}]-\mathbb E_{f\sim D_0}\Pr[A^f\text{ accepts}]\right|\le4\sum_{t<q}\sqrt{\rho_t}.$$
--
--   The input set is finite, D₀ assigns independent uniform signs, every good-record family contains the empty record and has orthonormal record vectors, and each ρₜ bounds the probability that either S or S△{x} is bad for every fixed |S|≤t and x. The algorithm and its operations are fixed independently of the hidden parameter.
--
--   This result supplies a supporting statement for Theorem 10.1, Theorem 11.4.
--
--   Differences from the source:
--   - encoding: sign-valued Boolean oracle on a finite input set → the bit-valued oracle on the same input set, with sign (-1)^bit; reason: the change of encoding is bijective and uses the same standard XOR value oracle
--   - encoding: hidden random parameter u and conditional oracle distributions → an arbitrary probability space with measurable finite oracle weights and measurable good-record events; reason: these are the implicit requirements for the displayed probabilities and expectations; no discrete or finite restriction is imposed on u
--   - encoding: orthonormal record vectors and q standard value queries → their exact weighted-character inner-product equations, and a maximum of q queries for the published adaptive model; reason: the real equations equal the complex inner products because the record vectors have real amplitudes; the algorithm is fixed independently of u
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, Lemma 9.2, p. 43

import Mathlib
import Definitions.Def_QTolTest1673_Unified_Supplement_Records

open scoped BigOperators
open Classical QAlgorithms FourierDimTesting102.Quantum
open Filter MeasureTheory

namespace QTolTest1673.Unified.Supplement

/-- Lemma 9.2, p.43: arbitrary hidden probability space and all general quantum algorithms. -/
theorem lemma_9_2 {X : Type} [Fintype X] [DecidableEq X]
    {U : Type*} [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ]
    (D : U → PMF (X → Bool))
    (hD : ∀ f, Measurable (fun u => (D u f).toReal))
    (G : U → Set (Finset X)) (hG : ∀ S, MeasurableSet {u | S ∈ G u})
    (hgood : ∀ u, GoodRecords (D u) (G u))
    (q : ℕ) (ρ : ℕ → ℝ) (hρ : ∀ t < q, 0 ≤ ρ t)
    (hbad : ∀ t < q, ∀ S : Finset X, S.card ≤ t → ∀ x : X,
      μ.real {u | S ∉ G u ∨ symmDiff S {x} ∉ G u} ≤ ρ t)
    (A : AdaptiveQueryAlg X Bool) (hq : ∀ f, A.maxQueries f ≤ q) :
  |(∫ u, acceptMean A (D u) ∂μ) -
    acceptMean A (PMF.uniformOfFintype (X → Bool))| ≤
      4 * ∑ t ∈ Finset.range q, Real.sqrt (ρ t) := by sorry

end QTolTest1673.Unified.Supplement
