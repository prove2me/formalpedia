-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_norm_le_one_iff_isIntegralElem_padicInt_f628f916acb3
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_norm_le_one_iff_isIntegralElem_padicInt_f628f916acb3
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:39:31.399217+00:00
-- url     : https://prove2.me/theorems/90917811-c1c9-4374-a1e9-134e419ecec4
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B norm le one iff is Integral Elem padic Int f628f916acb3: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Fo
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B norm le one iff is Integral Elem padic Int f628f916acb3 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B norm le one iff is Integral Elem padic Int f628f916acb3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/NormLeOneIffIsIntegralElemOfEquiv.lean#L25-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/NormLeOneIffIsIntegralElemOfEquiv.lean#L25-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_NormLeOneIffIsIntegralElemOfEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open IsDedekindDomain NumberField Polynomial Rat.HeightOneSpectrum

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_norm_le_one_iff_isIntegralElem_padicInt_f628f916acb3 (p : ℕ) [Fact p.Prime] {K : Type*}
    [NormedField K] [NormedAlgebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] (x : K) :
    ‖x‖ ≤ 1 ↔ ((algebraMap ℚ_[p] K).comp (algebraMap ℤ_[p] ℚ_[p])).IsIntegralElem x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«FourB».«norm_le_one_iff_isIntegralElem_padicInt» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_norm_le_one_iff_isIntegralElem_padicInt_f628f916acb3
