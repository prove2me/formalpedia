-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureWInfinityDifferentMultiplicity
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureWInfinityDifferentMultiplicity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T21:08:11.380597+00:00
-- url     : https://prove2.me/theorems/f95e35f0-9197-4822-8c27-ec78df0792da
-- title:
--   F256 Garcia Stichtenoth: source Closure WInfinity Different Multiplicity
-- statement:
--   The different at every genuine infinity-fibre prime is `2(β-1)`, with
--   the existing common Galois ramification index `β`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureFibreDifferent.lean#L83-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureFibreDifferent.lean#L83-L98

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWGlobalPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureFibreDifferent
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] closureDifferent_modelDedekind closureDifferent_modelFinite
  closureDifferent_modelFraction closureDifferent_modelTorsionFree
variable (m : ℕ)
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.fibreDifferent_baseAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.fibreDifferent_baseFraction
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.fibreDifferent_baseFaithful
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.fibreDifferent_baseDVR
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.fibreDifferent_ambientAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.fibreDifferent_baseTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.fibreDifferent_ambientTorsionFree
set_option maxHeartbeats 1000000

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureWInfinityDifferentMultiplicity (P : SourceGaloisWInfinityPrime m) :
    multiplicity P.1 (sourceClosurePlaceDifferentIdeal m (sourceGaloisWClosureInfinityPlace m)) =
      2 * (sourceGaloisWInfinityRamificationIndex m - 1) := by sorry
