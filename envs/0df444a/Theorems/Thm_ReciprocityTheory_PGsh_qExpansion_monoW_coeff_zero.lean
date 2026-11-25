-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_qExpansion_monoW_coeff_zero
-- name    : ReciprocityTheory.PGsh.qExpansion_monoW_coeff_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:09:42.592537+00:00
-- url     : https://prove2.me/theorems/b7b39ea7-e584-4528-858f-7eb10af6c7e4
-- title:
--   PGsh: q Expansion mono W coeff zero
-- statement:
--   The PGsh construction uses the q Expansion mono W coeff zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/QExpansionMonoWCoeffZero.lean#L38-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/QExpansionMonoWCoeffZero.lean#L38-L44

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_Eisenstein4CoeffBound
import Definitions.Def_ReciprocityTheory_DualLattices_QExpansionMonoWCoeffZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.PGsh
open UpperHalfPlane hiding I
open Complex ModularForm ModularFormClass MatrixGroups EisensteinSeries

theorem ReciprocityTheory.PGsh.qExpansion_monoW_coeff_zero {w a : ℕ} (h : a ∈ monoIdx w) :
    (qExpansion 1 (monoW w a)).coeff 0 = 1 := by sorry
