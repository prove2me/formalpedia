-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousMap_allTarget_rees_chartCoordinate_isWeaklyRegular
-- name    : PermanentRollout.homogeneousMap_allTarget_rees_chartCoordinate_isWeaklyRegular
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.782607+00:00
-- url     : https://prove2.me/theorems/2c739c78-96c9-49b4-8503-7a943996764f
-- title:
--   PermanentRollout.homogeneousMap_allTarget_rees_chartCoordinate_isWeaklyRegular
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra

theorem PermanentRollout.homogeneousMap_allTarget_rees_chartCoordinate_isWeaklyRegular
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ) (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : Fin k → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0) :
    RingTheory.Sequence.IsWeaklyRegular
      (MvPolynomial (Fin (k + 1)) ℂ ⧸
        homogeneousMapAllTargetReesChartIdeal k (1 : ℂ))
      (List.ofFn fun i : Fin k =>
        Ideal.Quotient.mk
          (homogeneousMapAllTargetReesChartIdeal k (1 : ℂ))
          (homogeneousMapAllTargetReesCoordinate F target e i)) := by sorry
