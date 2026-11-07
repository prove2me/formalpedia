-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_card_typeRows_of_dvd
-- name    : QEC.Coding.FiberBundle.RandomPartition.card_typeRows_of_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:20:02.290826+00:00
-- url     : https://prove2.me/theorems/bfae66b4-0341-4a64-bb3f-18139d05c855
-- title:
--   Random Partition: card type Rows of dvd
-- statement:
--   When the cyclic type partition divides the number of base checks, every
--   type receives exactly `3r/typeCount` rows.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1491-L1534
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1491-L1534

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

theorem QEC.Coding.FiberBundle.RandomPartition.card_typeRows_of_dvd
    (r typeCount : Nat) [NeZero typeCount]
    (hDvd : typeCount ∣ 3 * r)
    (τ : Fin typeCount) :
    (typeRows r typeCount τ).card = (3 * r) / typeCount := by sorry
