-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_weightReductionForwardMap1_vertical_auxiliary_expansion
-- name    : QEC.Coding.FiberBundle.weightReductionForwardMap1_vertical_auxiliary_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:14:02.078564+00:00
-- url     : https://prove2.me/theorems/64eca87b-a0d0-481f-b501-5f3d97ffebde
-- title:
--   Fiber Bundle: weight Reduction Forward Map1 vertical auxiliary expansion
-- statement:
--   The Fiber Bundle construction uses the weight Reduction Forward Map1 vertical auxiliary expansion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L104-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L104-L152

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

theorem QEC.Coding.FiberBundle.weightReductionForwardMap1_vertical_auxiliary_expansion
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (b : baseOne)
    (k : Fin (Fintype.card
      (ClassicalWeightReduction.BitNeighbor R b) - 1))
    (j : fiberOne) :
    weightReductionForwardMap1 D h
        (reducedQubitBasisWord D
          (Sum.inr
            (Sum.inr
              (⟨b, k⟩ : ClassicalWeightReduction.AuxiliaryCheck R), j))) =
      ∑ i : Fin (Fintype.card
          (ClassicalWeightReduction.BitNeighbor R b)),
        ClassicalWeightReduction.pathVertexSuffix (F := ZMod 2) k i •
          Pi.single
            (Sum.inr
              ((ClassicalWeightReduction.bitIncidenceAt R b i).1.1,
                (D.connection b
                  (ClassicalWeightReduction.bitIncidenceAt R b i).1.1
                  ).onOne j)) 1 := by sorry
