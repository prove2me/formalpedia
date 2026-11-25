-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_prod_split_70d0fbdbab85
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_prod_split_70d0fbdbab85
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:10:24.963827+00:00
-- url     : https://prove2.me/theorems/11d88c0e-6fff-407e-97c2-826bae918f63
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR divided Difference Expansion prod split 70d0fbdbab85: P2 M Ground Theory Heights  Heights Numbers DVR divided Difference Expansion prod split 70d0fbdbab
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR divided Difference Expansion prod split 70d0fbdbab85 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR divided Difference Expansion prod split 70d0fbdbab85 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinDivDiffExpansion.lean#L12-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinDivDiffExpansion.lean#L12-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinDivDiffExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR.dividedDifferenceExpansion

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_prod_split_70d0fbdbab85 {M : Type*} [CommMonoid M] {r : ℕ} (l : Fin r) (f : Fin r → M) :
    ∏ j, f j = (∏ j ∈ Finset.univ.filter (fun j => j < l), f j) * f l *
      ∏ j ∈ Finset.univ.filter (fun j => l < j), f j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«dividedDifferenceExpansion».«prod_split» := P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_prod_split_70d0fbdbab85
