-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIncDomain_isHomogeneous_linForm_5e6e05fede50
-- name    : P2M_GroundTheory_Heights__Heights_ChartIncDomain_isHomogeneous_linForm_5e6e05fede50
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:28:01.448841+00:00
-- url     : https://prove2.me/theorems/f3547609-e8df-4e99-959d-4b5e9b58ec35
-- title:
--   P2 M Ground Theory Heights  Heights Chart Inc Domain is Homogeneous lin Form 5e6e05fede50: P2 M Ground Theory Heights  Heights Chart Inc Domain is Homogeneous lin Form 5e6e05fede50
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Inc Domain is Homogeneous lin Form 5e6e05fede50 construction uses the P2 M Ground Theory Heights  Heights Chart Inc Domain is Homogeneous lin Form 5e6e05fede50 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartIncDomain.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartIncDomain.lean#L25-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartIncDomain
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartIncDomain

theorem P2M_GroundTheory_Heights__Heights_ChartIncDomain_isHomogeneous_linForm_5e6e05fede50 {F : Type*} [CommRing F] {n : ℕ} (t : Fin n → F) :
    (linForm t).IsHomogeneous 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIncDomain».«isHomogeneous_linForm» := P2M_GroundTheory_Heights__Heights_ChartIncDomain_isHomogeneous_linForm_5e6e05fede50
