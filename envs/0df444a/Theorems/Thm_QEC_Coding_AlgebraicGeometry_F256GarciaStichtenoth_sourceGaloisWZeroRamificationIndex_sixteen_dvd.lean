-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWZeroRamificationIndex_sixteen_dvd
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroRamificationIndex_sixteen_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:14:02.945201+00:00
-- url     : https://prove2.me/theorems/f56efe13-dace-409e-b703-c1a266a74f63
-- title:
--   F256 Garcia Stichtenoth: source Galois WZero Ramification Index sixteen dvd
-- statement:
--   The common ramification index above `w = 0` is divisible by sixteen at
--   every source closure level containing the first recursion step.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWZeroRamification.lean#L457-L484
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWZeroRamification.lean#L457-L484

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSeedTranslation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWZeroRamification
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 4000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroRamification_sourceZeroClosureBaseAlgebraPinned
attribute [local instance 4000] sourceGaloisWZeroRamification_sourceZeroClosureBaseAlgebraPinned
attribute [local instance 4000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroRamification_sourceZeroClosureBaseSMulPinned
attribute [local instance 4000] sourceGaloisWZeroRamification_sourceZeroClosureBaseSMulPinned
attribute [local instance 4000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroRamification_sourceZeroClosureBaseModulePinned
attribute [local instance 4000] sourceGaloisWZeroRamification_sourceZeroClosureBaseModulePinned
attribute [local instance 4000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroRamification_sourceZeroClosureConstantAlgebraPinned
attribute [local instance 4000] sourceGaloisWZeroRamification_sourceZeroClosureConstantAlgebraPinned
attribute [local instance 4000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroRamification_sourceZeroClosureConstantSMulPinned
attribute [local instance 4000] sourceGaloisWZeroRamification_sourceZeroClosureConstantSMulPinned
attribute [local instance 4000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroRamification_sourceZeroClosureConstantModulePinned
attribute [local instance 4000] sourceGaloisWZeroRamification_sourceZeroClosureConstantModulePinned
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroRamification_sourceZeroClosureConstantBaseTowerPinned
attribute [local instance] sourceGaloisWZeroRamification_sourceZeroClosureConstantBaseTowerPinned
attribute [local instance 4000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroRamification_sourceZeroClosureRatFuncAlgebraPinned
attribute [local instance 4000] sourceGaloisWZeroRamification_sourceZeroClosureRatFuncAlgebraPinned
attribute [local instance 4000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroRamification_sourceZeroClosureRatFuncSMulPinned
attribute [local instance 4000] sourceGaloisWZeroRamification_sourceZeroClosureRatFuncSMulPinned
attribute [local instance 4000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroRamification_sourceZeroClosureRatFuncModulePinned
attribute [local instance 4000] sourceGaloisWZeroRamification_sourceZeroClosureRatFuncModulePinned
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroRamification_sourceZeroClosureRatFuncTowerPinned
attribute [local instance] sourceGaloisWZeroRamification_sourceZeroClosureRatFuncTowerPinned

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroRamificationIndex_sixteen_dvd (m : ℕ) :
    16 ∣ sourceGaloisWZeroRamificationIndex (m + 1) := by sorry
