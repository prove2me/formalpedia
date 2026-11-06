-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureGenus_eq_source_formula
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureGenus_eq_source_formula
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:35:25.7162+00:00
-- url     : https://prove2.me/theorems/e0ed2567-a493-4042-85ce-09082928c3c5
-- title:
--   F256 Garcia Stichtenoth: source Closure Genus eq source formula
-- statement:
--   The paper's rational genus formula for the constructed normal closure,
--   with n the cardinality of its actual selected rational-place enumeration.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureGenus.lean#L70-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureGenus.lean#L70-L105

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureCanonicalDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureFullConstants
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Theorem
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureGenus
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureGenus_eq_source_formula (m : ℕ) :
    (sourceClosureGenus m : ℚ) = 1 + (sourceGaloisClosureSelectedLength m : ℚ) / 15 *
      (1 - 1 / (sourceGaloisWZeroRamificationIndex m : ℚ) -
        1 / (sourceGaloisWInfinityRamificationIndex m : ℚ)) := by sorry
