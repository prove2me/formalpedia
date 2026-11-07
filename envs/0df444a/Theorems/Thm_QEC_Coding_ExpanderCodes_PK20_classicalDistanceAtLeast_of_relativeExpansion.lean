-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_classicalDistanceAtLeast_of_relativeExpansion
-- name    : QEC.Coding.ExpanderCodes.PK20.classicalDistanceAtLeast_of_relativeExpansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:41:07.195713+00:00
-- url     : https://prove2.me/theorems/c9225a1f-c84e-4405-8c11-2ee598cd0fcb
-- title:
--   PK20: classical Distance At Least of relative Expansion
-- statement:
--   A nonzero kernel word must lie outside the relative expansion ball.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ClassicalFactor.lean#L29-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ClassicalFactor.lean#L29-L60

import Definitions.Def_QEC_Coding_ExpanderCodes_AlmostLinear
import Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalRowReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalFactor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct
open QEC.Coding.DistanceBalancing

theorem QEC.Coding.ExpanderCodes.PK20.classicalDistanceAtLeast_of_relativeExpansion
    {bit check : Type}
    [Fintype bit] [DecidableEq bit]
    [Fintype check] [DecidableEq check]
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check)
    {radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator : Nat}
    (hExpansionNumerator : 0 < expansionNumerator)
    (hExpansion : Y.SmallSetExpandingAtRelativeRadius
      radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator) :
    ClassicalDistanceAtLeast (LinearMap.toMatrix' Y)
      (classicalDistanceLowerBound (Fintype.card bit)
        radiusNumerator radiusDenominator) := by sorry
