-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actual_preimage_chain
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.actual_preimage_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:29:59.285223+00:00
-- url     : https://prove2.me/theorems/76c160ce-4da2-49f1-a030-eb62c62524d0
-- title:
--   BDL26 History Syndrome Sensitivity: actual preimage chain
-- statement:
--   The complete representative/potential chain is constructed from top validity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Preimages.lean#L166-L206
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Preimages.lean#L166-L206

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Preimages
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.actual_preimage_chain (sigma : TopInput S n) :
    ∃ (E : ∀ a : LevelIndex n, (SuffixData S n).family.Cochain1 a)
      (P : ∀ i : StepIndex n,
        (indexedFamily S (n+2)).Cochain0 (LevelTwoHistory.physicalStep i).succ),
      (indexedFamily S (n+2)).coboundary1 (TopIndex (n+2)) (E (TopIndex n)) = sigma.val ∧
      (∀ a, (SuffixData S n).family.coboundary1 a (E a) = actualReadout S n sigma a) ∧
      (∀ i, ((indexedDecoderData S (n+2)).selectedMap (LevelTwoHistory.physicalStep i)).map1
        (E i.castSucc) = physicalUpperError S n i (E i.succ) +
          (actualStep S (n+2) (LevelTwoHistory.physicalStep i)
            (actualInputs S n sigma i.succ)).correction +
          (indexedFamily S (n+2)).coboundary0 (LevelTwoHistory.physicalStep i).succ (P i)) ∧
      (∀ i, (indexedFamily S (n+2)).coboundary1 (LevelTwoHistory.physicalStep i).succ
        ((indexedFamily S (n+2)).coboundary0 (LevelTwoHistory.physicalStep i).succ (P i)) = 0) := by sorry
