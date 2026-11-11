-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_c2_pair_weight
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.c2_pair_weight
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T11:30:34.804336+00:00
-- url     : https://prove2.me/theorems/eff37178-e496-43f6-82d4-315a389002f7
-- title:
--   BDL26 History Syndrome Sensitivity: c2 pair weight
-- statement:
--   Physical C2 is the actual final input, not a fabricated below-base snapshot.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity.lean#L108-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity.lean#L108-L113

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Preimages
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26RXCoarseInfluence BDL26RXInfluenceBounds MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (d : Nat) (i : StepIndex d)
variable (n : Nat)

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.c2_pair_weight (sigma tau : TopInput S n) :
    HammingWeight (actualReadout S n sigma 0 + actualReadout S n tau 0) ≤
      57 ^ ((n+1)/2) * HammingWeight (sigma.val + tau.val) := by sorry
