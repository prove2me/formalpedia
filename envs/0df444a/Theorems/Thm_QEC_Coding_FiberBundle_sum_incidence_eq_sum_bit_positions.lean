-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_sum_incidence_eq_sum_bit_positions
-- name    : QEC.Coding.FiberBundle.sum_incidence_eq_sum_bit_positions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:13:57.89441+00:00
-- url     : https://prove2.me/theorems/7cd7af06-bbda-4920-9fd9-110c20c27dce
-- title:
--   Fiber Bundle: sum incidence eq sum bit positions
-- statement:
--   The Fiber Bundle construction uses the sum incidence eq sum bit positions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L87-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L87-L102

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

theorem QEC.Coding.FiberBundle.sum_incidence_eq_sum_bit_positions
    {M : Type*} [AddCommMonoid M]
    (f : ClassicalWeightReduction.Incidence R → M) :
    (∑ e, f e) =
      ∑ b : baseOne,
        ∑ i : Fin (Fintype.card
          (ClassicalWeightReduction.BitNeighbor R b)),
          f (ClassicalWeightReduction.bitIncidenceAt R b i) := by sorry
