-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticLiteral_allPrime_normalizing_correction
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticLiteral_allPrime_normalizing_correction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:06:18.882012+00:00
-- url     : https://prove2.me/theorems/31771600-3da6-4747-af34-45cf0f516e96
-- title:
--   F256 Garcia Stichtenoth: quadratic Literal all Prime normalizing correction
-- statement:
--   Any normalized lower parameter admits the source's explicit correction
--   after a literal quadratic step at a specified upper prime. Regular branches
--   use zero correction; the ramified pair uses the residue-square lift.
--   Neither upper-place compatibility nor a different formula is an input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticNormalization.lean#L247-L307
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticNormalization.lean#L247-L307

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ArtinSchreierCancellation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticNormalization
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticLiteral_allPrime_normalizing_correction
    {K L : Type*} [_root_.Field K] [_root_.Field L]
    [Algebra F256 K] [Algebra F256 L] [Algebra K L] [Algebra.IsSeparable K L]
    (P : GlobalPlace F256 K) [Finite P.residueField]
    [Algebra P.valuationRing L] [IsScalarTower P.valuationRing K L]
    [IsDedekindDomain (integralClosure P.valuationRing L)]
    [IsFractionRing (integralClosure P.valuationRing L) L]
    [Module.IsTorsionFree P.valuationRing (integralClosure P.valuationRing L)]
    (H : IsDedekindDomain.HeightOneSpectrum (integralClosure P.valuationRing L))
    [H.asIdeal.LiesOver (IsLocalRing.maximalIdeal P.valuationRing)]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤)
    (ha : P.order a = -1 ∨ 0 ≤ P.order a)
    (b : K) (hb : P.order b = -1 ∨ 0 ≤ P.order b) :
    ∃ c : L,
      (c = 0 ∨ (integralClosurePlace (k := F256) H).order c = -1) ∧
      ((integralClosurePlace (k := F256) H).order (algebraMap K L b + c ^ 2 + c) = -1 ∨
        0 ≤ (integralClosurePlace (k := F256) H).order (algebraMap K L b + c ^ 2 + c)) := by sorry
