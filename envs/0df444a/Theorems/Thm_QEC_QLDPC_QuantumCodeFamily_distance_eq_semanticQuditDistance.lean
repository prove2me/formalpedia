-- Prove2me | Theorems.Thm_QEC_QLDPC_QuantumCodeFamily_distance_eq_semanticQuditDistance
-- name    : QEC.QLDPC.QuantumCodeFamily.distance_eq_semanticQuditDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:27:55.924196+00:00
-- url     : https://prove2.me/theorems/6fa6c01a-ea9f-4174-ac9a-c1809005ac6b
-- title:
--   Quantum Code Family: distance eq semantic Qudit Distance
-- statement:
--   Indexed distance is the semantic local-operator distance of the indexed code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/QuantumCodeFamily.lean#L71-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/QuantumCodeFamily.lean#L71-L76

import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
import Definitions.Def_QEC_Coding_QLDPC_QuantumCodeFamily
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_distance_eq_semanticQuditDistance

set_option autoImplicit false
noncomputable section
open QEC QEC.QLDPC
universe u v w
open QEC.QLDPC.QuantumCodeFamily
variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]

theorem QEC.QLDPC.QuantumCodeFamily.distance_eq_semanticQuditDistance
    (F : QuantumCodeFamily A ι κ) (a : A) :
    F.distance a = semanticQuditDistance
      (uniformQuditDimensions (ι := ι a) (F.presentation a).alphabetSize)
      (F.presentation a).code := by sorry
