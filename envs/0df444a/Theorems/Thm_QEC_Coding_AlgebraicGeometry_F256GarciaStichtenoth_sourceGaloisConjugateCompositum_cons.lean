-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisConjugateCompositum_cons
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisConjugateCompositum_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:24:37.456236+00:00
-- url     : https://prove2.me/theorems/d6afc84d-7bbf-437b-befb-b177af916ac8
-- title:
--   F256 Garcia Stichtenoth: source Galois Conjugate Compositum cons
-- statement:
--   Inserting one conjugate source field adjoins its actual field range to
--   the preceding finite compositum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceNormalClosureFiniteCompositum.lean#L38-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceNormalClosureFiniteCompositum.lean#L38-L59

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosure
import Mathlib.Order.CompactlyGenerated.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosureFiniteCompositum
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisConjugateCompositum_cons (m : ℕ)
    (s : Finset (SourceField m →ₐ[GaloisBaseField]
      SourceGaloisClosureAmbient))
    (f : SourceField m →ₐ[GaloisBaseField]
      SourceGaloisClosureAmbient)
    (hf : f ∉ s) :
    sourceGaloisConjugateCompositum m (s.cons f hf) =
      sourceGaloisConjugateCompositum m s ⊔ f.fieldRange := by sorry
