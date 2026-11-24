-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Div_BlockChangeDet_det_blockDiagonal__eq_prod_ef1b50bb1ef0
-- name    : P2M_GlobalTheory_Div_BlockChangeDet_det_blockDiagonal__eq_prod_ef1b50bb1ef0
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:04:13.474054+00:00
-- url     : https://prove2.me/theorems/06df4189-796d-4611-98e1-e307aae81e27
-- title:
--   P2 M Global Theory Div Block Change Det det block Diagonal  eq prod ef1b50bb1ef0: P2 M Global Theory Div Block Change Det det block Diagonal  eq prod ef1b50bb1ef0
-- statement:
--   The P2 M Global Theory Div Block Change Det det block Diagonal  eq prod ef1b50bb1ef0 construction uses the P2 M Global Theory Div Block Change Det det block Diagonal  eq prod ef1b50bb1ef0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DetBlockChangeOfBasisViaTwoFamiliesImplicit.lean#L7-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DetBlockChangeOfBasisViaTwoFamiliesImplicit.lean#L7-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetBlockChangeOfBasisViaTwoFamiliesImplicit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Div GlobalTheory.Div.BlockChangeDet
open Matrix

theorem P2M_GlobalTheory_Div_BlockChangeDet_det_blockDiagonal__eq_prod_ef1b50bb1ef0 {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
    {κ : ι → Type} [∀ c, Fintype (κ c)] [∀ c, DecidableEq (κ c)]
    (M : ∀ c, Matrix (κ c) (κ c) R) :
    (Matrix.blockDiagonal' M).det = ∏ c, (M c).det := by sorry

alias «GlobalTheory».«Div».«BlockChangeDet».«det_blockDiagonal'_eq_prod» := P2M_GlobalTheory_Div_BlockChangeDet_det_blockDiagonal__eq_prod_ef1b50bb1ef0
