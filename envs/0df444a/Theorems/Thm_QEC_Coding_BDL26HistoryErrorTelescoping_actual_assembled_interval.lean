-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_actual_assembled_interval
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.actual_assembled_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:24:30.434056+00:00
-- url     : https://prove2.me/theorems/0630295f-5ba5-4a30-a9d2-06d264e28827
-- title:
--   BDL26 History Error Telescoping: actual assembled interval
-- statement:
--   The BDL26 History Error Telescoping construction uses the actual assembled interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L312-L322
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L312-L322

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open scoped Classical
universe u v w
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26HistoryErrorTelescoping.actual_assembled_interval (sigma : TopInput S n) (b : LevelIndex n)
    (u : (SuffixData S n).family.Cochain1 b)
    (hu : (SuffixData S n).family.coboundary1 b u = actualReadout S n sigma b)
    (a c : LevelIndex n) (hac : a.val ≤ c.val) (hcb : c.val ≤ b.val) :
    descentWord S n b u c hcb + assembledPrefix S n sigma c =
      intervalMap1 (SuffixData S n) a c hac
        (descentWord S n b u a (hac.trans hcb) + assembledPrefix S n sigma a) +
        (SuffixData S n).family.coboundary0 c
          (accumulatedPotential S n b u a c.val hcb hac) := by sorry
