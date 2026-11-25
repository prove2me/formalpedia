-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IsMultiHomogIdeal_sup_4e558288843a
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_IsMultiHomogIdeal_sup_4e558288843a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:07:23.755799+00:00
-- url     : https://prove2.me/theorems/e104d1a4-57d5-4326-aba3-df02bf5858d2
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Is Multi Homog Ideal sup 4e558288843a: P2 M Ground Theory Heights  Heights Numbers DVR Is Multi Homog Ideal sup 4e558288843a
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Is Multi Homog Ideal sup 4e558288843a construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Is Multi Homog Ideal sup 4e558288843a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ImportsSide.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ImportsSide.lean#L14-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LocCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PColonMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsSide
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
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_IsMultiHomogIdeal_sup_4e558288843a {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
    {I J : Ideal (MRing ι R)} (hI : IsMultiHomogIdeal I) (hJ : IsMultiHomogIdeal J) :
    IsMultiHomogIdeal (I ⊔ J) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«IsMultiHomogIdeal».«sup» := P2M_GroundTheory_Heights__Heights_NumbersDVR_IsMultiHomogIdeal_sup_4e558288843a
