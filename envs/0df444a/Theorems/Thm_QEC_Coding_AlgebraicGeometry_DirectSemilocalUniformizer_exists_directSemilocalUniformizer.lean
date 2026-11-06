-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectSemilocalUniformizer_exists_directSemilocalUniformizer
-- name    : QEC.Coding.AlgebraicGeometry.DirectSemilocalUniformizer.exists_directSemilocalUniformizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:44:10.760736+00:00
-- url     : https://prove2.me/theorems/f943e2c8-5395-4762-927f-1c3005ec63a9
-- title:
--   Direct Semilocal Uniformizer: exists direct Semilocal Uniformizer
-- statement:
--   There is one nonzero direct integral element having normalized order one
--   at every actual factor over a fixed direct base prime.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/SemilocalUniformizer.lean#L126-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/SemilocalUniformizer.lean#L126-L182

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalLogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalUniformizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectSemilocalUniformizer
open scoped Polynomial RatFunc nonZeroDivisors BigOperators
open UniqueFactorizationMonoid
open DirectIntegralDifferentialResidue
open DirectFactorSemilocalLogarithmicResidue
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalUniformizer._p2m_local_instance_46770e045f_37
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalUniformizer._p2m_local_instance_46770e045f_42

theorem QEC.Coding.AlgebraicGeometry.DirectSemilocalUniformizer.exists_directSemilocalUniformizer
    (p : IsDedekindDomain.HeightOneSpectrum (R k)) :
    ∃ t : B k F, t ≠ 0 ∧
      ∀ P : (factors
        (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
        GlobalPlace.order
            (AffinePlace.globalPlace k F (directFactorPlace k F p P))
            (algebraMap (B k F) F t) = 1 := by sorry
