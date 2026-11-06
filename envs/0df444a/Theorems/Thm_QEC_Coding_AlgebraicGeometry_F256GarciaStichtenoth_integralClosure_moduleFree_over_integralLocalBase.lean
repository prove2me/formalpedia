-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_integralClosure_moduleFree_over_integralLocalBase
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.integralClosure_moduleFree_over_integralLocalBase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:13:52.15192+00:00
-- url     : https://prove2.me/theorems/19837c52-4adf-4ea3-9ad7-99f8690404de
-- title:
--   F256 Garcia Stichtenoth: integral Closure module Free over integral Local Base
-- statement:
--   An integral closure over a Dedekind extension of a local domain is free
--   over that intermediate Dedekind ring.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/LocalIntegralClosureFree.lean#L42-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/LocalIntegralClosureFree.lean#L42-L57

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.PID
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_LocalIntegralClosureFree
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.integralClosure_moduleFree_over_integralLocalBase
    (A B K L C : Type*)
    [CommRing A] [CommRing B] [Field K] [Field L] [CommRing C]
    [IsDomain A] [IsLocalRing A] [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B]
    [Module.IsTorsionFree A B]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [Algebra C L] [IsIntegralClosure C B L]
    [Algebra B C] [IsScalarTower B C L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.IsTorsionFree B L] :
    Module.Free B C := by sorry
