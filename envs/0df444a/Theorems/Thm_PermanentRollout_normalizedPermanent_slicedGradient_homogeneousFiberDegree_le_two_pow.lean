-- Prove2me | Theorems.Thm_PermanentRollout_normalizedPermanent_slicedGradient_homogeneousFiberDegree_le_two_pow
-- name    : PermanentRollout.normalizedPermanent_slicedGradient_homogeneousFiberDegree_le_two_pow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.904517+00:00
-- url     : https://prove2.me/theorems/db81cdcc-b47a-49b3-967c-681000bcb628
-- title:
--   PermanentRollout.normalizedPermanent_slicedGradient_homogeneousFiberDegree_le_two_pow
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section

theorem PermanentRollout.normalizedPermanent_slicedGradient_homogeneousFiberDegree_le_two_pow
    {n m k : ℕ}
    (circuit : ArithmeticCircuit (Fin n × Fin n))
    (hpermanent : circuit.polynomial = permanent n)
    (substitution : (Fin n × Fin n) → FreeAffineInput (Fin m))
    (P : MvPolynomial (Fin m) ℂ)
    (c : ℂ) (hc : c ≠ 0)
    (hspecialization :
      MvPolynomial.aeval (fun ij => (substitution ij).polynomial)
          (permanent n) = MvPolynomial.C c * P)
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (A : (Fin m → ℂ) →ₗ[ℂ] (Fin k → ℂ))
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (slicedGradientPolynomial P W A i).IsHomogeneous e)
    (hzero : ∀ point : Fin k → ℂ,
      (∀ i, MvPolynomial.eval point
        (slicedGradientPolynomial P W A i) = 0) ↔ point = 0) :
    e ^ k ≤ 2 ^ (3 * circuit.size) := by sorry
