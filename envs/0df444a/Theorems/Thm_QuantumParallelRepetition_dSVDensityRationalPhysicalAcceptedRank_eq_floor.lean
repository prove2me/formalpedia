-- Prove2me | Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalPhysicalAcceptedRank_eq_floor
-- name    : QuantumParallelRepetition.dSVDensityRationalPhysicalAcceptedRank_eq_floor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.843984+00:00
-- url     : https://prove2.me/theorems/bf5efd46-f7e1-4e91-9909-ed5b62307b98
-- title:
--   QuantumParallelRepetition.dSVDensityRationalPhysicalAcceptedRank_eq_floor
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
open scoped BigOperators ComplexOrder MatrixOrder

theorem QuantumParallelRepetition.dSVDensityRationalPhysicalAcceptedRank_eq_floor
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (ξ : BipartiteUnitVector d) (i : Fin d) :
    (dSVDensityRationalPhysicalAcceptedRank
      w N ξ i).val =
      Nat.floor
        (dSVRationalSoftPass w
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i) * (N : ℝ)) := by sorry
