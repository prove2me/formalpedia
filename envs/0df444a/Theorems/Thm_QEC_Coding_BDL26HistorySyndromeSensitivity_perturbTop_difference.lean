-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_perturbTop_difference
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.perturbTop_difference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T10:58:53.655233+00:00
-- url     : https://prove2.me/theorems/54b237aa-b6e6-4bad-a55e-aae5a119bcab
-- title:
--   BDL26 History Syndrome Sensitivity: perturb Top difference
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the perturb Top difference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity.lean#L76-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity.lean#L76-L82

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

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.perturbTop_difference (sigma : TopInput S n)
    (e : (indexedFamily S (n+2)).Cochain1 (TopIndex (n+2))) :
    sigma.val + (perturbTop S n sigma e).val =
      (indexedFamily S (n+2)).coboundary1 (TopIndex (n+2)) e := by sorry
