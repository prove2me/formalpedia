-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianBundle_normDegree_eq_deg_sub_462229a1e5e8
-- name    : P2M_GroundTheory_Heights__Heights_HermitianBundle_normDegree_eq_deg_sub_462229a1e5e8
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:57:59.540514+00:00
-- url     : https://prove2.me/theorems/52caedb3-f2e4-5b6f-a038-6a65be1526e6
-- title:
--   P2 M Ground Theory Heights  Heights Hermitian Bundle norm Degree eq deg sub 462229a1e5e8: P2 M Ground Theory Heights  Heights Hermitian Bundle norm Degree eq deg sub 462229a1e5e8
-- statement:
--   The P2 M Ground Theory Heights  Heights Hermitian Bundle norm Degree eq deg sub 462229a1e5e8 construction uses the P2 M Ground Theory Heights  Heights Hermitian Bundle norm Degree eq deg sub 462229a1e5e8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Slopes/PRelSlopeQuot.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Slopes/PRelSlopeQuot.lean#L17-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PExactSequence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PChainSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Slopes_PRelSlopeQuot
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
open NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.HermitianBundle
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_HermitianBundle_normDegree_eq_deg_sub_462229a1e5e8 (E : HermitianBundle K) (F : Submodule (𝓞 K) E.carrier) :
    E.normDegree F = (E.sub F).deg := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermitianBundle».«normDegree_eq_deg_sub» := P2M_GroundTheory_Heights__Heights_HermitianBundle_normDegree_eq_deg_sub_462229a1e5e8
