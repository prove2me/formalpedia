-- Prove2me | Theorems.Thm_QTolTest1673_Unified_Supplement_lemma_8_2
-- name    : QTolTest1673.Unified.Supplement.lemma_8_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:27:02.828304+00:00
-- url     : https://prove2.me/theorems/155d829b-4784-4d67-9ddc-43e601a9de34
-- title:
--   Lemma 8.2 — Simultaneous NO distance promise
-- statement:
--   Simultaneous NO distance promise: for k sufficiently large, with balanced shifts b_i and independent uniform NO rows, Pr_{ρ,y∼N_src}[dist(f_y, J_{n0,k}) < 61/128] ≤ e^{−K}.
--
--   $$\Pr_{\rho,y}[\operatorname{dist}(f_y,J_{n_0,k})<61/128]\le e^{-K}.$$
--
--   This result supplies a supporting statement for Theorem 8.5.
--
--   Differences from the source:
--   - encoding: sign-valued functions on one-based binary coordinates → bit-valued functions on Fin-indexed binary coordinates, with sign (-1)^bit; reason: the published models give a bijective representation and preserve the value oracle and uniform Hamming distance
--   - encoding: n₀=2K+a variables and independent uniform injections and rows → a+2K coordinates, address first, and the uniform average over encoding-table pairs; reason: coordinate permutation preserves junta distance; the product uniform law is exactly the required independent sampling
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, Lemma 8.2, p. 35

import Mathlib
import Definitions.Def_QTolTest1673_Unified_Supplement_Rows

open scoped BigOperators
open Classical QAlgorithms FourierDimTesting102.Quantum
open Filter MeasureTheory

namespace QTolTest1673.Unified.Supplement

/-- Lemma 8.2, p.35: the encoding and NO table are independent uniform choices. -/
theorem lemma_8_2 :
  ∃ K₀ : ℕ, ∀ k ≥ K₀, a8 k ≤ k ∧ 6 ≤ K8 k ∧ 3 ≤ a8 k ∧
    ∀ shifts : V (a8 k) → V 3, Balanced shifts →
      frac (fun p : Encoding (a8 k) (K8 k) × Table (a8 k) =>
        distToSet (rowFn p.1 shifts p.2) (junta (n8 k) k) < 61/128) ≤
          Real.exp (-(K8 k : ℝ)) := by sorry

end QTolTest1673.Unified.Supplement
