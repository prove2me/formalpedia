-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_norm_cpow_neg_le_one__4b558658281b
-- name    : P2M_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_norm_cpow_neg_le_one__4b558658281b
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:56:45.733296+00:00
-- url     : https://prove2.me/theorems/22e4fd41-1d34-4c11-afdc-8d2312ea500a
-- title:
--   P2 M Formalism Hermitian Lattices Ext Primitive Character Casts ZD norm cpow neg le one  4b558658281b: P2 M Formalism Hermitian Lattices Ext Primitive Character Casts ZD norm cpow neg le one  4b558658
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext Primitive Character Casts ZD norm cpow neg le one  4b558658281b construction uses the P2 M Formalism Hermitian Lattices Ext Primitive Character Casts ZD norm cpow neg le one  4b558658281b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZBlock.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZBlock.lean#L9-L13

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

theorem P2M_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_norm_cpow_neg_le_one__4b558658281b {n : ℕ} (hn : 1 ≤ n) {w : ℂ} (hw : 0 ≤ w.re) : ‖(n : ℂ) ^ (-w)‖ ≤ 1 := by sorry

alias «Formalism».«HermitianLattices».«Ext».«PrimitiveCharacterCasts».«ZD».«norm_cpow_neg_le_one'» := P2M_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_norm_cpow_neg_le_one__4b558658281b
