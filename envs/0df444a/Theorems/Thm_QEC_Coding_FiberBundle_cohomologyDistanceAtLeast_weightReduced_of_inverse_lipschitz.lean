-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_cohomologyDistanceAtLeast_weightReduced_of_inverse_lipschitz
-- name    : QEC.Coding.FiberBundle.cohomologyDistanceAtLeast_weightReduced_of_inverse_lipschitz
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:14:03.795397+00:00
-- url     : https://prove2.me/theorems/cd99de42-8031-4211-a51d-b6d3ff974220
-- title:
--   Fiber Bundle: cohomology Distance At Least weight Reduced of inverse lipschitz
-- statement:
--   A proved transpose-inverse Lipschitz bound converts an original-bundle
--   cohomology distance bound into the corresponding reduced-bundle bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L53-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L53-L64

import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
open scoped BigOperators
universe u
variable {baseZero baseOne fiberZero fiberOne : Type u}
variable [Fintype baseZero] [DecidableEq baseZero]
variable [Fintype baseOne] [DecidableEq baseOne]
variable [Fintype fiberZero] [DecidableEq fiberZero]
variable [Fintype fiberOne] [DecidableEq fiberOne]
variable (D : Data baseZero baseOne fiberZero fiberOne)
local notation "R" => baseSupportRelation D

theorem QEC.Coding.FiberBundle.cohomologyDistanceAtLeast_weightReduced_of_inverse_lipschitz
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    {d L : Nat}
    (hDistance : CohomologyDistanceAtLeast D d)
    (hLipschitz : ∀ x,
      HammingWeight
          (wordLinearMapTranspose (weightReductionInverseMap1 D h) x) ≤
        L * HammingWeight x) :
    CohomologyDistanceAtLeast (weightReducedData D) (d / L) := by sorry
