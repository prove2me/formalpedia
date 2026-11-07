-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_sum_sampleRowEitherViolationIndicator_selected_le_heavyIncidentViolationCount
-- name    : QEC.Coding.FiberBundle.RandomPartition.sum_sampleRowEitherViolationIndicator_selected_le_heavyIncidentViolationCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:25:31.207326+00:00
-- url     : https://prove2.me/theorems/eaa552da-7084-42a6-883e-3fe7241dd9cf
-- title:
--   Random Partition: sum sample Row Either Violation Indicator selected le heavy Incident Violation Count
-- statement:
--   The selected-row OR count is bounded pointwise by the deterministic
--   incident-violation count.  This bridge is independent of all type shifts.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3019-L3065
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3019-L3065

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomPartition.sum_sampleRowEitherViolationIndicator_selected_le_heavyIncidentViolationCount
    {r typeCount ell : Nat} [NeZero typeCount]
    (sample : Sample r)
    (typeShifts : Fin typeCount → Fin (ell - 1))
    (x : Word (ZMod 2) (Fin (4 * r)))
    (types : Finset (Fin typeCount))
    (outWord inWord :
      Fin typeCount → Word (ZMod 2) (Fin (4 * r))) :
    (∑ a ∈ selectedTypeRows r typeCount types,
        sampleRowEitherViolationIndicator
          x outWord inWord a sample) ≤
      (TwistGraph.heavyIncidentViolationCount
        (baseSample sample) (twistSample sample typeShifts)
        x types outWord inWord : Real) := by sorry
