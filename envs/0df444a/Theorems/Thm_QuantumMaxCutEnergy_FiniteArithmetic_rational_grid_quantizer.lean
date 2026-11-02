-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_FiniteArithmetic_rational_grid_quantizer
-- name    : QuantumMaxCutEnergy.FiniteArithmetic.rational_grid_quantizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T16:01:16.305465+00:00
-- url     : https://prove2.me/theorems/853710cd-aee2-4282-a440-34ba13e6fcb5
-- title:
--   A binary polynomial-time rational grid quantizer
-- statement:
--   There is one polynomial-time rational function $f$ such that, for every positive integer $M$ and every rational $q\ge-1$,
--
--   $$q-\frac1M<f(M,q)\le q.$$
--
--   The function preserves $[-1,1]$ and satisfies $f(M,1)=1$. The time bound is polynomial in the binary encoding lengths of $M$ and $q$.
-- source:
--   Exact rational arithmetic: f(M,q)=floor(M(q+1))/M−1 for M>0 and q≥−1. The implementation composes the verified binary integer and rational primitives in QuantumMaxCutFiniteNumericRuntime.

import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Mathlib

theorem QuantumMaxCutEnergy.FiniteArithmetic.rational_grid_quantizer :
    ∃ f : ℕ × ℚ → ℚ,
      Nonempty (OAI.MetricKMedian.Binary.PolyProgram
        (OAI.MetricKMedian.Binary.encodePair Nat.bits OAI.MetricKMedian.Binary.Ratio.encode)
        OAI.MetricKMedian.Binary.Ratio.encode f) ∧
      ∀ M : ℕ, 0 < M → ∀ q : ℚ, -1 ≤ q →
        f (M, q) ≤ q ∧ q < f (M, q) + 1 / (M : ℚ) ∧
        |f (M, q) - q| ≤ 1 / (M : ℚ) ∧
        (q ≤ 1 → -1 ≤ f (M, q) ∧ f (M, q) ≤ 1) ∧
        f (M, 1) = 1 := by sorry
