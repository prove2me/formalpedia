-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_zero_not_mem_normalModelSubmonoid_47a2efab4a46
-- name    : P2M_GroundTheory_Heights__Heights_zero_not_mem_normalModelSubmonoid_47a2efab4a46
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:52:23.478363+00:00
-- url     : https://prove2.me/theorems/00ac3c28-60d7-51c1-b8e2-956a5cb8673d
-- title:
--   P2 M Ground Theory Heights  Heights zero not mem normal Model Submonoid 47a2efab4a46: P2 M Ground Theory Heights  Heights zero not mem normal Model Submonoid 47a2efab4a46
-- statement:
--   The P2 M Ground Theory Heights  Heights zero not mem normal Model Submonoid 47a2efab4a46 construction uses the P2 M Ground Theory Heights  Heights zero not mem normal Model Submonoid 47a2efab4a46 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalisationModelLocalization.lean#L23-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalisationModelLocalization.lean#L23-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalisationModelLocalization
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
open MvPolynomial ComplexSets
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_zero_not_mem_normalModelSubmonoid_47a2efab4a46 {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) (q : Fin n → ℂ) (hq : q ∈ zeroSet J) :
    (0 : MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) ∉ normalModelSubmonoid M q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«zero_not_mem_normalModelSubmonoid» := P2M_GroundTheory_Heights__Heights_zero_not_mem_normalModelSubmonoid_47a2efab4a46
