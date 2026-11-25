-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mk_rename_mem_normalModelSubmonoid_b73a888102e6
-- name    : P2M_GroundTheory_Heights__Heights_mk_rename_mem_normalModelSubmonoid_b73a888102e6
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:49:18.021778+00:00
-- url     : https://prove2.me/theorems/3960c29a-bd55-44ac-a341-b5bad5b7cf77
-- title:
--   P2 M Ground Theory Heights  Heights mk rename mem normal Model Submonoid b73a888102e6: P2 M Ground Theory Heights  Heights mk rename mem normal Model Submonoid b73a888102e6
-- statement:
--   The P2 M Ground Theory Heights  Heights mk rename mem normal Model Submonoid b73a888102e6 construction uses the P2 M Ground Theory Heights  Heights mk rename mem normal Model Submonoid b73a888102e6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalisationModelLocalization.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalisationModelLocalization.lean#L17-L21

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

theorem P2M_GroundTheory_Heights__Heights_mk_rename_mem_normalModelSubmonoid_b73a888102e6 {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) (q : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) (hf : eval q f ≠ 0) :
    Ideal.Quotient.mk M.ideal (rename Sum.inl f) ∈ normalModelSubmonoid M q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mk_rename_mem_normalModelSubmonoid» := P2M_GroundTheory_Heights__Heights_mk_rename_mem_normalModelSubmonoid_b73a888102e6
