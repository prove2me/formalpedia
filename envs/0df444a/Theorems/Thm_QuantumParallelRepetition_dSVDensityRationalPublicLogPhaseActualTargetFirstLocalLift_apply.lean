-- Prove2me | Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift_apply
-- name    : QuantumParallelRepetition.dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:44.608116+00:00
-- url     : https://prove2.me/theorems/facd98ac-67b8-49a5-b035-c1830eedf0b5
-- title:
--   QuantumParallelRepetition.dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift_apply
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
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

theorem QuantumParallelRepetition.dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift_apply
    (B N d L m : ℕ)
    (U : Matrix.unitaryGroup
      (DSVDensityRationalPublicLogPhaseHistoryLocalIndex
        B N d L) ℂ)
    (a b : DSVDensityRationalPublicLogPhaseHistoryLocalIndex
      B N d L) (i j : Fin m) :
    dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift
      B N d L m U
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
        B N d L m (a, i))
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
        B N d L m (b, j)) =
      if i = j then U a b else 0 := by sorry
