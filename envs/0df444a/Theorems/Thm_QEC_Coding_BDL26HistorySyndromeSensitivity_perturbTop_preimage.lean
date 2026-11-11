-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_perturbTop_preimage
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.perturbTop_preimage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T10:58:56.07177+00:00
-- url     : https://prove2.me/theorems/8af47262-a64b-4524-ae17-126ea05b7c22
-- title:
--   BDL26 History Syndrome Sensitivity: perturb Top preimage
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the perturb Top preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity.lean#L67-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity.lean#L67-L74

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

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.perturbTop_preimage (sigma : TopInput S n)
    (e : (indexedFamily S (n+2)).Cochain1 (TopIndex (n+2))) :
    ∃ a : (indexedFamily S (n+2)).Cochain1 (TopIndex (n+2)),
      (indexedFamily S (n+2)).coboundary1 (TopIndex (n+2)) a = sigma.val ∧
      (indexedFamily S (n+2)).coboundary1 (TopIndex (n+2)) (a+e) =
        (perturbTop S n sigma e).val := by sorry
