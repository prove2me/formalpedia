-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_scalar_klein_log
-- name    : QEC.Semantics.FiniteMatrixEntropy.scalar_klein_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:41:08.831118+00:00
-- url     : https://prove2.me/theorems/67af792c-279d-456d-8799-3ce4734b5c3c
-- title:
--   Finite Matrix Entropy: scalar klein log
-- statement:
--   The scalar Klein inequality in the form used after spectral expansion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L61-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L61-L70

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder Kronecker TensorProduct
noncomputable section
open QEC.Semantics.FiniteMatrixEntropy

theorem QEC.Semantics.FiniteMatrixEntropy.scalar_klein_log {a b : Real} (ha : 0 <= a) (hb : 0 < b) :
    a - b <= a * (Real.log a - Real.log b) := by sorry
