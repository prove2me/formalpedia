-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianBundle_normDegree_le_rank_mul_39ef423f891f
-- name    : P2M_GroundTheory_Heights__Heights_HermitianBundle_normDegree_le_rank_mul_39ef423f891f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:46.804086+00:00
-- url     : https://prove2.me/theorems/b78fcf01-b100-4cf0-bdeb-9fc433a405e6
-- title:
--   P2 M Ground Theory Heights  Heights Hermitian Bundle norm Degree le rank mul 39ef423f891f: P2 M Ground Theory Heights  Heights Hermitian Bundle norm Degree le rank mul 39ef423f891f
-- statement:
--   The P2 M Ground Theory Heights  Heights Hermitian Bundle norm Degree le rank mul 39ef423f891f construction uses the P2 M Ground Theory Heights  Heights Hermitian Bundle norm Degree le rank mul 39ef423f891f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/DegreeTopEqArithDegree.lean#L29-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/DegreeTopEqArithDegree.lean#L29-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_DegreeTopEqArithDegree
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

theorem P2M_GroundTheory_Heights__Heights_HermitianBundle_normDegree_le_rank_mul_39ef423f891f {K : Type} [Field K] [NumberField K]
    (E : HermitianBundle.{0} K) (G : Submodule (𝓞 K) E.carrier) (m : ℝ)
    (hm : E.slopeMax ≤ (m : EReal)) : E.normDegree G ≤ E.rank G * m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermitianBundle».«normDegree_le_rank_mul» := P2M_GroundTheory_Heights__Heights_HermitianBundle_normDegree_le_rank_mul_39ef423f891f
