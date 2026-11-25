-- Prove2me | Theorems.Thm_P2M_GlobalTheory_JR_NormalFormL_inv_act__a1785aba4025
-- name    : P2M_GlobalTheory_JR_NormalFormL_inv_act__a1785aba4025
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:06:47.293035+00:00
-- url     : https://prove2.me/theorems/afd001df-35ed-4d41-9da5-7bbe7139f01c
-- title:
--   P2 M Global Theory JR Normal Form L inv act  a1785aba4025: P2 M Global Theory JR Normal Form L inv act  a1785aba4025
-- statement:
--   The P2 M Global Theory JR Normal Form L inv act  a1785aba4025 construction uses the P2 M Global Theory JR Normal Form L inv act  a1785aba4025 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean#L79-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean#L79-L88

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

theorem P2M_GlobalTheory_JR_NormalFormL_inv_act__a1785aba4025 (g : GL (Fin r) k) (Y : Gl r k) : inv (act g Y) = inv Y := by sorry

alias «GlobalTheory».«JR».«NormalFormL».«inv_act'» := P2M_GlobalTheory_JR_NormalFormL_inv_act__a1785aba4025
