-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_exists_simplePole_baseChange_correction
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.exists_simplePole_baseChange_correction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:06:46.748846+00:00
-- url     : https://prove2.me/theorems/24b5f3ea-7686-42fd-9a5c-6d5b1a63849f
-- title:
--   F256 Garcia Stichtenoth: exists simple Pole base Change correction
-- statement:
--   The source's residue-square correction, on any compatible pair of places.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticNormalization.lean#L66-L199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticNormalization.lean#L66-L199

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ArtinSchreierCancellation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticNormalization
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.exists_simplePole_baseChange_correction
    {K L : Type*} [_root_.Field K] [_root_.Field L]
    [Algebra F256 K] [Algebra K L] [Algebra F256 L]
    (P : GlobalPlace F256 K) [Finite P.residueField]
    (Q : GlobalPlace F256 L)
    (z y : K) (x : L)
    (hz : P.order z = -1) (hy : P.order y = -1)
    (hx : Q.order x = -1)
    (hequation : x ^ 2 + x = algebraMap K L z)
    (horder_algebraMap : ∀ v : K, v ≠ 0 →
      Q.order (algebraMap K L v) = 2 * P.order v) :
    ∃ c : L,
      Q.order c = -1 ∧
        (Q.order (algebraMap K L y + c ^ 2 + c) = -1 ∨
          0 ≤ Q.order (algebraMap K L y + c ^ 2 + c)) := by sorry
