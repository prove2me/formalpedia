-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceSupportedBorn
-- name    : QuantumParallelRepetition.unconditionalActualFairSourceSupportedBorn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:48.934586+00:00
-- url     : https://prove2.me/theorems/182c0a68-636a-4802-8cab-539a65bdcb7f
-- title:
--   QuantumParallelRepetition.unconditionalActualFairSourceSupportedBorn
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
  Matrix.Norms.L2Operator InnerProductSpace

theorem QuantumParallelRepetition.unconditionalActualFairSourceSupportedBorn
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (a₀ : A) (b₀ : B)
    (h : ExactLocallySampleableTuple X Y A B D)
    (supported : exactLocallySampleableLaw G n S D h ≠ 0)
    {P N L m : ℕ} (phases : 0 < P) (grid : 0 < N)
    (harmonic : 0 < m)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (j : Fin L) :
    quadraticExpectation
      (integratorActualC485WinningEffect
        G n S D a₀ b₀ (P := P) (N := N) (m := m)
        j h.2.1 h.2.2.1)
      (integratorActualC485SourceVector
        (B := P) (N := N) (m := m) width schedule
        (exactGlobalHistoryFinGamma G n S D h.2.2.2 h.2.1)
        (exactGlobalHistoryFinPhi G n S D h.2.2.2 h.2.2.1)
        (exactSourceTuplePsi G n S D h) j) =
      ‖integratorActualC485SourceVector
        (B := P) (N := N) (m := m) width schedule
        (exactGlobalHistoryFinGamma G n S D h.2.2.2 h.2.1)
        (exactGlobalHistoryFinPhi G n S D h.2.2.2 h.2.2.1)
        (exactSourceTuplePsi G n S D h) j‖ ^ 2 *
        exactSourceConditionalWinningProbability G n S D h := by sorry
