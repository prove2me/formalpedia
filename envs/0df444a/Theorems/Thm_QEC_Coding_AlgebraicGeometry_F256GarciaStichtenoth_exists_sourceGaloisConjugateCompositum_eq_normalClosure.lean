-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_exists_sourceGaloisConjugateCompositum_eq_normalClosure
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.exists_sourceGaloisConjugateCompositum_eq_normalClosure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:24:59.058522+00:00
-- url     : https://prove2.me/theorems/2efd68ea-598f-4a8d-af7d-9ba8f69692a8
-- title:
--   F256 Garcia Stichtenoth: exists source Galois Conjugate Compositum eq normal Closure
-- statement:
--   Finitely many actual conjugate copies of source level `m` generate its
--   constructed normal closure inside the fixed separable closure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceNormalClosureFiniteCompositum.lean#L63-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceNormalClosureFiniteCompositum.lean#L63-L92

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosure
import Mathlib.Order.CompactlyGenerated.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosureFiniteCompositum
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.exists_sourceGaloisConjugateCompositum_eq_normalClosure (m : ℕ) :
    ∃ s : Finset (SourceField m →ₐ[GaloisBaseField]
        SourceGaloisClosureAmbient),
      sourceGaloisConjugateCompositum m s =
        IntermediateField.normalClosure GaloisBaseField (SourceField m)
          SourceGaloisClosureAmbient := by sorry
