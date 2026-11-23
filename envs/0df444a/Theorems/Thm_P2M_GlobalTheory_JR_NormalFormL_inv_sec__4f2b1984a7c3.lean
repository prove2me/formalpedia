-- Prove2me | Theorems.Thm_P2M_GlobalTheory_JR_NormalFormL_inv_sec__4f2b1984a7c3
-- name    : P2M_GlobalTheory_JR_NormalFormL_inv_sec__4f2b1984a7c3
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:16.945953+00:00
-- url     : https://prove2.me/theorems/66a99d67-c58e-4a39-bd2f-4b5f1fdbbfa9
-- title:
--   P2 M Global Theory JR Normal Form L inv sec  4f2b1984a7c3: P2 M Global Theory JR Normal Form L inv sec  4f2b1984a7c3
-- statement:
--   The P2 M Global Theory JR Normal Form L inv sec  4f2b1984a7c3 construction uses the P2 M Global Theory JR Normal Form L inv sec  4f2b1984a7c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean#L95-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean#L95-L100

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

theorem P2M_GlobalTheory_JR_NormalFormL_inv_sec__4f2b1984a7c3 (a : Inv r k) : inv (sec a) = a := by sorry

alias «GlobalTheory».«JR».«NormalFormL».«inv_sec'» := P2M_GlobalTheory_JR_NormalFormL_inv_sec__4f2b1984a7c3
