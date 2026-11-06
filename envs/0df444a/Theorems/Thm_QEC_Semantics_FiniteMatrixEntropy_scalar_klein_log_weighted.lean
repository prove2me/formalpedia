-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_scalar_klein_log_weighted
-- name    : QEC.Semantics.FiniteMatrixEntropy.scalar_klein_log_weighted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:41:17.855193+00:00
-- url     : https://prove2.me/theorems/73359ece-d47a-4b6a-b4ac-c3ac622e0fd3
-- title:
--   Finite Matrix Entropy: scalar klein log weighted
-- statement:
--   The scalar Klein inequality is stable under a nonnegative overlap weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L73-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean#L73-L76

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

theorem QEC.Semantics.FiniteMatrixEntropy.scalar_klein_log_weighted {a b w : Real}
    (ha : 0 <= a) (hb : 0 < b) (hw : 0 <= w) :
    w * (a - b) <= w * (a * (Real.log a - Real.log b)) := by sorry
