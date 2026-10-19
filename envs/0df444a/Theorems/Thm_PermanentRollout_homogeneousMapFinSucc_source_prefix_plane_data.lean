-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousMapFinSucc_source_prefix_plane_data
-- name    : PermanentRollout.homogeneousMapFinSucc_source_prefix_plane_data
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:35.41423+00:00
-- url     : https://prove2.me/theorems/9e1000a3-716b-40c6-962b-63f0b694b8a2
-- title:
--   PermanentRollout.homogeneousMapFinSucc_source_prefix_plane_data
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators

theorem PermanentRollout.homogeneousMapFinSucc_source_prefix_plane_data
    {n : ℕ}
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) ℂ)
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : Fin (n + 1) → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0) :
    ∃ c : Fin 1 → Fin (n + 1) → ℂ,
      LinearIndependent ℂ c ∧
      MvPolynomial.zeroLocus ℂ
        (Ideal.span (Set.range fun i : Fin n => F i.castSucc) ⊔
          Ideal.span (Set.range fun i : Fin 1 =>
            permanentRolloutLinearCoordinateCombination (n + 1) (c i))) =
        ({0} : Set (Fin (n + 1) → ℂ)) := by sorry
