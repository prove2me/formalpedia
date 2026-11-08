-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_firstBalancing_distanceBounds
-- name    : QEC.Coding.ExpanderCodes.PK20.firstBalancing_distanceBounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:38:04.594227+00:00
-- url     : https://prove2.me/theorems/cc070b2d-a2d2-43d7-bc48-b58b6c69a2f9
-- title:
--   PK20: first Balancing distance Bounds
-- statement:
--   The PK20 construction uses the first Balancing distance Bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TwoStepBalancing.lean#L102-L124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TwoStepBalancing.lean#L102-L124

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Dimension
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Definitions.Def_QEC_Coding_ExpanderCodes_TwoStepBalancing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.DistanceBalancing
universe u
variable {xZero xOne xTwo bitOne checkOne bitTwo checkTwo : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype bitOne] [DecidableEq bitOne]
variable [Fintype checkOne] [DecidableEq checkOne]
variable [Fintype bitTwo] [DecidableEq bitTwo]
variable [Fintype checkTwo] [DecidableEq checkTwo]

theorem QEC.Coding.ExpanderCodes.PK20.firstBalancing_distanceBounds
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y : Word (ZMod 2) bitOne →ₗ[ZMod 2] Word (ZMod 2) checkOne)
    {dHomology dCohomology dClassical : Nat}
    (hSurjective : Function.Surjective Y)
    (hHomology : MiddleHomologyDistanceAtLeast X dHomology)
    (hCohomology : MiddleCohomologyDistanceAtLeast X dCohomology)
    (hClassical : ClassicalDistanceAtLeast
      (LinearMap.toMatrix' Y) dClassical) :
    MiddleHomologyDistanceAtLeast (firstBalancedComplex X Y)
        (dClassical * dHomology) ∧
      MiddleCohomologyDistanceAtLeast (firstBalancedComplex X Y)
        dCohomology := by sorry
