-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockSign_mul_self_a12250e20b18
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockSign_mul_self_a12250e20b18
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:41.05411+00:00
-- url     : https://prove2.me/theorems/5ce90668-3010-4a03-8ec3-8087a015e5fe
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag block Sign mul self a12250e20b18: P2 M Ground Theory Heights  Heights Rest Terms Flag block Sign mul self a12250e20b18
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag block Sign mul self a12250e20b18 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag block Sign mul self a12250e20b18 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L57-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L57-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockSign_mul_self_a12250e20b18 (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) :
    blockSign f N w * blockSign f N w = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«blockSign_mul_self» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockSign_mul_self_a12250e20b18
