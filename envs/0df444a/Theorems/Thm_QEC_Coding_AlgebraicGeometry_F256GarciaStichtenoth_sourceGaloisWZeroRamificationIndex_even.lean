-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWZeroRamificationIndex_even
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroRamificationIndex_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:14:09.099958+00:00
-- url     : https://prove2.me/theorems/a07fc693-7e8a-44d7-8954-c99815bc2bb2
-- title:
--   F256 Garcia Stichtenoth: source Galois WZero Ramification Index even
-- statement:
--   The common zero-fibre ramification index is even at every level
--   containing the first source step.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWZeroRamification.lean#L488-L492
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWZeroRamification.lean#L488-L492

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroRamificationIndex_even (m : ℕ) :
    Even (sourceGaloisWZeroRamificationIndex (m + 1)) := by sorry
