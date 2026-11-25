-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIncDomain_aeval_smul_of_isHomogeneous_7eddd2d173b5
-- name    : P2M_GroundTheory_Heights__Heights_ChartIncDomain_aeval_smul_of_isHomogeneous_7eddd2d173b5
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:27:49.044991+00:00
-- url     : https://prove2.me/theorems/9e5cb5bd-2044-403e-b8cd-e22149263a94
-- title:
--   P2 M Ground Theory Heights  Heights Chart Inc Domain aeval smul of is Homogeneous 7eddd2d173b5: P2 M Ground Theory Heights  Heights Chart Inc Domain aeval smul of is Homogeneous 7eddd2d173b5
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Inc Domain aeval smul of is Homogeneous 7eddd2d173b5 construction uses the P2 M Ground Theory Heights  Heights Chart Inc Domain aeval smul of is Homogeneous 7eddd2d173b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartIncDomain.lean#L13-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartIncDomain.lean#L13-L23

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

theorem P2M_GroundTheory_Heights__Heights_ChartIncDomain_aeval_smul_of_isHomogeneous_7eddd2d173b5 {R S σ : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d) (c : S) (x : σ → S) :
    aeval (c • x) p = c ^ d * aeval x p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIncDomain».«aeval_smul_of_isHomogeneous» := P2M_GroundTheory_Heights__Heights_ChartIncDomain_aeval_smul_of_isHomogeneous_7eddd2d173b5
