-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_labelCount_insert
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.labelCount_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:16:56.852204+00:00
-- url     : https://prove2.me/theorems/91b49447-c7b0-4fbb-ad93-3876a1611d0d
-- title:
--   Resampling: label Count insert
-- statement:
--   The Resampling construction uses the label Count insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryWitness.lean#L120-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryWitness.lean#L120-L129

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessTrees
import Mathlib.Data.Finset.Max
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.labelCount_insert (root j k : I) (P : Finset (List I))
    (h : (attachmentCandidates G root j P).Nonempty) :
    labelCount root k (extendWitness G root j P) =
      labelCount root k P + if j = k then 1 else 0 := by sorry
