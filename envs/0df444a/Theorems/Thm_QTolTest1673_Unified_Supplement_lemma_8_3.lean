-- Prove2me | Theorems.Thm_QTolTest1673_Unified_Supplement_lemma_8_3
-- name    : QTolTest1673.Unified.Supplement.lemma_8_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:27:48.711067+00:00
-- url     : https://prove2.me/theorems/301dbc7b-4b63-4a2c-9a25-3aa699f88586
-- title:
--   Lemma 8.3 — Exact agreement on small row sets
-- statement:
--   Exact agreement on small row sets: there is δ>0 depending only on c such that, with probability 1−o(1) over the random encoding ρ as k→∞, the joint law of (y_i)_{i∈I} is the same under Y_src and N_src for every I with |I| < δK.
--
--   $$\Pr_\rho[\forall I,\ |I|<\delta K:\ \mathcal L(Y_I)=\mathcal L(N_I)]\ge1-p(k),\qquad p(k)\longrightarrow0.$$
--
--   This result supplies a supporting statement for Theorem 8.5.
--
--   Differences from the source:
--   - encoding: sign-valued functions on one-based binary coordinates → bit-valued functions on Fin-indexed binary coordinates, with sign (-1)^bit; reason: the published models give a bijective representation and preserve the value oracle and uniform Hamming distance
--   - encoding: probability 1−o(1), with δ depending only on fixed c → a positive δ before k, a nonnegative failure function p(k) tending to zero, and an eventual bound; reason: the source asymptotic failure probability is made explicit, including nonempty injection spaces
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, Lemma 8.3, p. 37

import Mathlib
import Definitions.Def_QTolTest1673_Unified_Supplement_Rows

open scoped BigOperators
open Classical QAlgorithms FourierDimTesting102.Quantum
open Filter MeasureTheory

namespace QTolTest1673.Unified.Supplement

/-- Lemma 8.3, p.37. δ is fixed before k, and the failure probability tends to zero. -/
theorem lemma_8_3 :
  ∃ δ : ℝ, 0 < δ ∧ ∃ p : ℕ → ℝ, (∀ k, 0 ≤ p k) ∧
    Filter.Tendsto p Filter.atTop (nhds 0) ∧ ∃ K₀ : ℕ,
      ∀ k ≥ K₀, 6 ≤ K8 k ∧
        frac (fun ρ : Encoding (a8 k) (K8 k) => ¬ Matching ρ δ) ≤ p k := by sorry

end QTolTest1673.Unified.Supplement
