-- Prove2me | Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalMixedSpectralAtomBlock_trace_eq
-- name    : QuantumParallelRepetition.dSVDensityRationalMixedSpectralAtomBlock_trace_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.843984+00:00
-- url     : https://prove2.me/theorems/c1c0c251-f270-4c61-afae-c8548fba1fb7
-- title:
--   QuantumParallelRepetition.dSVDensityRationalMixedSpectralAtomBlock_trace_eq
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | QuantumParallelRepetition | external Lean 4.33.1 validation; bundle SHA256 d8765170d1380c2591d50d87f9ea8fe3c5625537d968525072fc32b227592634

import Mathlib
import Definitions.Def_QuantumParallelRepetition
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.dSVDensityRationalMixedSpectralAtomBlock_trace_eq
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (a b : Bool) (k : Fin N) :
    (Matrix.trace
      (dSVDensityRationalMixedSpectralAtomBlock
        w N ξ ζ a b k)).re =
      ∑ i : Fin d, ∑ j : Fin d,
        if dSVDensityRationalProjectiveThresholdBin w N k
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ξ).isHermitian.eigenvalues i) = a ∧
          dSVDensityRationalProjectiveThresholdBin w N k
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ζ).isHermitian.eigenvalues j) = b
        then spectralAtomOverlap
          (dSVSoftBobLeftReducedDensity ξ)
          (dSVSoftBobLeftReducedDensity ζ)
          (dSVSoftBobLeftReducedDensity_posSemidef ξ)
          (dSVSoftBobLeftReducedDensity_posSemidef ζ) i j
        else 0 := by sorry
