-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_inh_restTerm_b831e71f17f7
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_inh_restTerm_b831e71f17f7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:03.923276+00:00
-- url     : https://prove2.me/theorems/d6d48131-63fe-4d0e-9d29-b18f68ea8f3a
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms inh rest Term b831e71f17f7: P2 M Ground Theory Heights  Heights Rest Terms inh rest Term b831e71f17f7
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms inh rest Term b831e71f17f7 construction uses the P2 M Ground Theory Heights  Heights Rest Terms inh rest Term b831e71f17f7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/InhabitantsElem.lean#L37-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/InhabitantsElem.lean#L37-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsElem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Inhabitants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_InhabitantsElem
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
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_inh_restTerm_b831e71f17f7 (τ τ' : Fin 1) :
    restTerm 1 (1 + 1) inhQ 2 τ (smallPowerSum 1 1 1 .last (2 - 1) τ') = -1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«inh_restTerm» := P2M_GroundTheory_Heights__Heights_RestTerms_inh_restTerm_b831e71f17f7
