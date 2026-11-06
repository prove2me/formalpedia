-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_uniformizerDerivative_isLocalDerivativeLatticePrincipalCutoff
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.uniformizerDerivative_isLocalDerivativeLatticePrincipalCutoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:23:55.555817+00:00
-- url     : https://prove2.me/theorems/08318fbb-cf47-4911-9698-18395e41e0a3
-- title:
--   Function Field Differential: uniformizer Derivative is Local Derivative Lattice Principal Cutoff
-- statement:
--   The derivative of the normalized uniformizer satisfies the complete
--   principal-cutoff contract.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/LocalUniformizerDerivative.lean#L233-L280
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/LocalUniformizerDerivative.lean#L233-L280

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_CanonicalDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalLogarithmicDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalUniformizerDerivative
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.uniformizerDerivative_isLocalDerivativeLatticePrincipalCutoff
    (P : GlobalPlace k F) :
    IsLocalDerivativeLatticePrincipalCutoff (k := k) (F := F) P
      (functionFieldDerivation (k := k) (F := F)
        (P.uniformizerInValuationRing : F)) := by sorry
