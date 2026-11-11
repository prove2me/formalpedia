-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_step_contraction
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.step_contraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:17:32.771641+00:00
-- url     : https://prove2.me/theorems/df7da181-4518-4d38-bba5-1d99b8135f43
-- title:
--   BDL26 Paired History Query Cone: step contraction
-- statement:
--   The actual one-step contraction, with the original physical parity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L424-L439
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L424-L439

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26PairedHistoryQueryCone.step_contraction (i : StepIndex n)
    (s : (SuffixData S n).family.Syndrome i.succ) :
    (if i.val % 2 = 0 then 2 else 1) *
      HammingWeight (actualStep S (n+2) (LevelTwoHistory.physicalStep i) s).coarse.val ≤
        HammingWeight s.val := by sorry
