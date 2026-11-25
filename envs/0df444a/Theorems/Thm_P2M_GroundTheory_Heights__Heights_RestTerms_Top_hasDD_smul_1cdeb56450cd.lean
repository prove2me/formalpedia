-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_smul_1cdeb56450cd
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_smul_1cdeb56450cd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:44.273751+00:00
-- url     : https://prove2.me/theorems/41800fc3-3b62-4520-ab0a-bddeedebbab8
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top has DD smul 1cdeb56450cd: P2 M Ground Theory Heights  Heights Rest Terms Top has DD smul 1cdeb56450cd
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top has DD smul 1cdeb56450cd construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top has DD smul 1cdeb56450cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L73-L75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
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
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_smul_1cdeb56450cd {f N : ℕ} {H P : RootRing f N} (b : ℚ) (h : HasDD f N H P) :
    HasDD f N (b • H) (b • P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«hasDD_smul» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_smul_1cdeb56450cd
