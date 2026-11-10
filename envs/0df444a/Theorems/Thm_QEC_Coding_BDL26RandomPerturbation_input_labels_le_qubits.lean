-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_input_labels_le_qubits
-- name    : QEC.Coding.BDL26RandomPerturbation.input_labels_le_qubits
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T02:35:44.83955+00:00
-- url     : https://prove2.me/theorems/0a3da63a-ea1c-487a-a5d8-97d4acd33bae
-- title:
--   BDL26 Random Perturbation: input labels le qubits
-- statement:
--   All labels used by the event algorithm are controlled by actual qubit count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/InputSize.lean#L73-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/InputSize.lean#L73-L83

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_InputSize
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26TannerLocalRegularity

theorem QEC.Coding.BDL26RandomPerturbation.input_labels_le_qubits (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (h : BoundedValence P) :
    Fintype.card P.X + Fintype.card P.Q + Fintype.card P.Z +
      Fintype.card (Triangle P) ≤ 65 * Fintype.card P.Q := by sorry
