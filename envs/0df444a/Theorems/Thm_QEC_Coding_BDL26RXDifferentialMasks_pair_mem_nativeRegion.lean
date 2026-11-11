-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_pair_mem_nativeRegion
-- name    : QEC.Coding.BDL26RXDifferentialMasks.pair_mem_nativeRegion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:37:53.735198+00:00
-- url     : https://prove2.me/theorems/5b85435c-38c5-4fca-bea3-05b39fe368e9
-- title:
--   BDL26 RXDifferential Masks: pair mem native Region
-- statement:
--   The BDL26 RXDifferential Masks construction uses the pair mem native Region property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L145-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L145-L151

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDifferentialMasks
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXQConcreteCoherence
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RXDifferentialMasks.pair_mem_nativeRegion (h : i.val % 2 = 0)
    (A : Finset (state S i.val).presentation.Q)
    (z : (state S i.val).presentation.Z) (copy : Fin 2) :
    ((rxData S depth i h).induced.zPairEquiv (z,copy)).val ∈ nativeRegion S depth i h A ↔
      ∃ q ∈ A, (state S i.val).presentation.qz q z = true := by sorry
