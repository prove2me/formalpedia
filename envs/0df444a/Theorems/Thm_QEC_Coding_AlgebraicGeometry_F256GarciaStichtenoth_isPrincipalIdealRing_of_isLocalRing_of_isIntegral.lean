-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_isPrincipalIdealRing_of_isLocalRing_of_isIntegral
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.isPrincipalIdealRing_of_isLocalRing_of_isIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:13:51.534448+00:00
-- url     : https://prove2.me/theorems/3f8f22bc-eef7-42f6-8331-807bc4aae950
-- title:
--   F256 Garcia Stichtenoth: is Principal Ideal Ring of is Local Ring of is Integral
-- statement:
--   A Dedekind integral extension of a local domain is a principal ideal
--   ring when it is torsion-free over the base.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/LocalIntegralClosureFree.lean#L20-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/LocalIntegralClosureFree.lean#L20-L38

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.PID
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_LocalIntegralClosureFree
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.isPrincipalIdealRing_of_isLocalRing_of_isIntegral
    (A B : Type*)
    [CommRing A] [CommRing B]
    [IsDomain A] [IsLocalRing A]
    [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B]
    [Module.IsTorsionFree A B] :
    IsPrincipalIdealRing B := by sorry
