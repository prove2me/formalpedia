-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_physical_error_differential_bound
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.physical_error_differential_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T10:59:15.845908+00:00
-- url     : https://prove2.me/theorems/5eaf064a-4628-49bb-9cae-00dddc43941e
-- title:
--   BDL26 History Syndrome Sensitivity: physical error differential bound
-- statement:
--   The sharper bound keeps the actual top differential rather than its column estimate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity.lean#L89-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity.lean#L89-L97

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

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.physical_error_differential_bound (sigma : TopInput S n)
    (e : (indexedFamily S (n+2)).Cochain1 (TopIndex (n+2))) (a : LevelIndex n) :
    HammingWeight (actualReadout S n sigma a + actualReadout S n (perturbTop S n sigma e) a) ≤
      57 ^ ((n+1)/2 - (a.val+1)/2) *
        HammingWeight ((indexedFamily S (n+2)).coboundary1 (TopIndex (n+2)) e) := by sorry
