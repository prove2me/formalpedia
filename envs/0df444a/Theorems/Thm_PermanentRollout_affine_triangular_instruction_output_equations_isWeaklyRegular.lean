-- Prove2me | Theorems.Thm_PermanentRollout_affine_triangular_instruction_output_equations_isWeaklyRegular
-- name    : PermanentRollout.affine_triangular_instruction_output_equations_isWeaklyRegular
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:38.420988+00:00
-- url     : https://prove2.me/theorems/bb618165-0651-4938-abeb-fcbc59fccdc2
-- title:
--   PermanentRollout.affine_triangular_instruction_output_equations_isWeaklyRegular
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

theorem PermanentRollout.affine_triangular_instruction_output_equations_isWeaklyRegular
    {k q : ℕ}
    (rhs : Fin q → MvPolynomial (Fin k ⊕ Fin q) ℂ)
    (gate : Fin q → MvPolynomial (Fin k) ℂ)
    (output : Fin k → MvPolynomial (Fin k ⊕ Fin q) ℂ)
    (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ)
    (hgate : ∀ j, gate j = affineGateGraphEvaluation gate (rhs j))
    (htop : ∀ j i : Fin q,
      Sum.inr i ∈ (rhs j).vars → i.val < j.val)
    (houtput : ∀ i, affineGateGraphEvaluation gate (output i) = F i)
    (hregular : RingTheory.Sequence.IsWeaklyRegular
      (MvPolynomial (Fin k) ℂ)
        (List.ofFn fun i : Fin k => F i - MvPolynomial.C (target i))) :
    RingTheory.Sequence.IsWeaklyRegular
      (MvPolynomial (Fin k ⊕ Fin q) ℂ)
      ((List.ofFn fun j : Fin q =>
          MvPolynomial.X (Sum.inr j) - rhs j) ++
        (List.ofFn fun i : Fin k =>
          output i - MvPolynomial.C (target i))) := by sorry
