-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureWZero_dz_order
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureWZero_dz_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T21:12:46.155692+00:00
-- url     : https://prove2.me/theorems/d649add6-9362-4c5e-ae4d-80d858a374a3
-- title:
--   F256 Garcia Stichtenoth: source Closure WZero dz order
-- statement:
--   The F256 Garcia Stichtenoth construction uses the source Closure WZero dz order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureFibreDifferentialOrder.lean#L27-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureFibreDifferentialOrder.lean#L27-L52

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_WBaseDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialPlaceTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureFibreDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureFibreDifferentialOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero

set_option autoImplicit false
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] closureDifferent_modelDedekind closureDifferent_modelFinite
  closureDifferent_modelFraction closureDifferent_modelTorsionFree
  fibreDifferent_baseAlgebra fibreDifferent_baseFraction fibreDifferent_baseFaithful
  fibreDifferent_baseDVR fibreDifferent_ambientAlgebra fibreDifferent_baseTower
  fibreDifferent_ambientTorsionFree
set_option maxHeartbeats 1000000

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureWZero_dz_order (m : ℕ) (P : SourceGaloisWZeroPrime m) :
    differentialOrder (sourceGaloisWZeroPlaceOfPrime m P)
      (functionFieldDifferentialGenerator (k := F256) (F := SourceGaloisClosureField m))
      functionFieldDifferentialGenerator_ne_zero =
        16 * (sourceGaloisWZeroRamificationIndex m : ℤ) - 2 := by sorry
