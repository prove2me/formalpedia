-- Prove2me | Theorems.Thm_PermanentRollout_sourceTreeBlockMatrix_permanent_eq_separated_minorSum
-- name    : PermanentRollout.sourceTreeBlockMatrix_permanent_eq_separated_minorSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:40.650338+00:00
-- url     : https://prove2.me/theorems/f24d6787-6df3-4a84-a85e-48b906ac1ba0
-- title:
--   PermanentRollout.sourceTreeBlockMatrix_permanent_eq_separated_minorSum
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.sourceTreeBlockMatrix_permanent_eq_separated_minorSum
    (b t s d : ℕ) (hdpos : 0 < d) (hd : d ≤ t)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d)
    (tree : BlockTree (Fin b))
    (hnodup : tree.leafList.Nodup)
    (hleaves : tree.leaves = Finset.univ) :
    rectangularPermanent
        (sourceBlockMatrix (b * t) s d
          (fun row column =>
            (MvPolynomial.X (row, column) :
              MvPolynomial (Fin (b * t) × Fin s) ℂ))
          (fun row column =>
            algebraMap ℂ (MvPolynomial (Fin (b * t) × Fin s) ℂ)
              (sourceTreeMatrix b t d hd ζ tree hnodup hleaves row column))) =
      (((s - d).factorial : ℕ) :
          MvPolynomial (Fin (b * t) × Fin s) ℂ) *
        algebraMap ℂ (MvPolynomial (Fin (b * t) × Fin s) ℂ)
          (((t - d).factorial : ℕ) : ℂ) *
        algebraMap ℂ (MvPolynomial (Fin (b * t) × Fin s) ℂ)
          ((((t.factorial : ℕ) : ℂ) ^ (b - 1))) *
        ∑ h : Fin b,
          algebraMap ℂ (MvPolynomial (Fin (b * t) × Fin s) ℂ)
              (subtreeCoefficient
                (((-1 : ℂ) ^ (d + 1)) * (2 : ℂ) ^ d) tree h) *
            MvPolynomial.rename
              (sourceRowBlockVariableEmbedding b t s h)
              (minorSum t s d) := by sorry
