-- Prove2me | Theorems.Thm_P2M_GlobalTheory_JR_NormalFormL_act_mul__049dd60a3f1d
-- name    : P2M_GlobalTheory_JR_NormalFormL_act_mul__049dd60a3f1d
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:06:55.67041+00:00
-- url     : https://prove2.me/theorems/42f5705d-f071-45c4-a898-e18500863ce9
-- title:
--   P2 M Global Theory JR Normal Form L act mul  049dd60a3f1d: P2 M Global Theory JR Normal Form L act mul  049dd60a3f1d
-- statement:
--   The P2 M Global Theory JR Normal Form L act mul  049dd60a3f1d construction uses the P2 M Global Theory JR Normal Form L act mul  049dd60a3f1d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean#L90-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean#L90-L93

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.NormalFormL
variable {k : Type} [Field k] {r : ℕ}

theorem P2M_GlobalTheory_JR_NormalFormL_act_mul__049dd60a3f1d (g h : GL (Fin r) k) (Y : Gl r k) : act (g * h) Y = act g (act h Y) := by sorry

alias «GlobalTheory».«JR».«NormalFormL».«act_mul'» := P2M_GlobalTheory_JR_NormalFormL_act_mul__049dd60a3f1d
