-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_ProjectiveLinearSize_exists_large_even_psl
-- name    : QEC.Coding.ExpanderCodes.ProjectiveLinearSize.exists_large_even_psl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:31:14.013435+00:00
-- url     : https://prove2.me/theorems/dfa778de-1fa4-4c71-ac90-8aaba4f29364
-- title:
--   Projective Linear Size: exists large even psl
-- statement:
--   The finite PSL₂ groups in even-degree extensions are cofinal in size;
--   the specialization and square root are actual elements, not certificate inputs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProjectiveLinearSize.lean#L65-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProjectiveLinearSize.lean#L65-L80

import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldQuadraticSplitting
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveLinearSize
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.ProjectiveLinearSize
open Matrix
variable {K : Type*} [Field K]

theorem QEC.Coding.ExpanderCodes.ProjectiveLinearSize.exists_large_even_psl (p N : ℕ) [hPrime : Fact p.Prime]
    (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0)
    (hNonSquare : ∀ r : ZMod p, r ^ 2 ≠ epsilon) :
    ∃ n : ℕ, 1 < n ∧
      N ≤ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p (2 * n))) ∧
      ∃ y r : GaloisField p (2 * n), y ≠ 0 ∧ 1 + y ≠ 0 ∧ r ≠ 0 ∧
        r ^ 2 = algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon ∧
        Irreducible (minpoly (ZMod p) y) ∧
        (minpoly (ZMod p) y).natDegree = 2 * n := by sorry
