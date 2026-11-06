-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureCanonicalDifferential_selected_residue
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureCanonicalDifferential_selected_residue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:32:26.063203+00:00
-- url     : https://prove2.me/theorems/6fe331c1-14ce-477c-a520-f6e8f662b149
-- title:
--   F256 Garcia Stichtenoth: source Closure Canonical Differential selected residue
-- statement:
--   At each actual enumerated rational point, eta has residue one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureCanonicalDifferential.lean#L122-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureCanonicalDifferential.lean#L122-L129

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferentialDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSelectedDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureCanonicalDifferential
set_option autoImplicit false
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.canonicalDifferentialModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.canonicalDifferentialSMul
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureCanonicalDifferential_selected_residue (m : ℕ)
    (j : Fin (sourceGaloisClosureSelectedLength m)) :
    Differential.simplePoleResidue (sourceGaloisClosureSelectedRationalPlace m j).place
      (sourceClosureCanonicalDifferentialAtPlace m (sourceGaloisClosureSelectedRationalPlace m j).place) =
        1 := by sorry
