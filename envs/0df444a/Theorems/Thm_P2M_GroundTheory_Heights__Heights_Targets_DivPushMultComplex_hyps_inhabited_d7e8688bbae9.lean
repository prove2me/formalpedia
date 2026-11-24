-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_DivPushMultComplex_hyps_inhabited_d7e8688bbae9
-- name    : P2M_GroundTheory_Heights__Heights_Targets_DivPushMultComplex_hyps_inhabited_d7e8688bbae9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:34:14.84714+00:00
-- url     : https://prove2.me/theorems/0bc78151-9b49-41f1-ac56-6c11105c8c88
-- title:
--   P2 M Ground Theory Heights  Heights Targets Div Push Mult Complex hyps inhabited d7e8688bbae9: P2 M Ground Theory Heights  Heights Targets Div Push Mult Complex hyps inhabited d7e8688bbae9
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Div Push Mult Complex hyps inhabited d7e8688bbae9 construction uses the P2 M Ground Theory Heights  Heights Targets Div Push Mult Complex hyps inhabited d7e8688bbae9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsDivPushMultComplex.lean#L19-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsDivPushMultComplex.lean#L19-L39

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsDivPushMultComplex
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_Targets_DivPushMultComplex_hyps_inhabited_d7e8688bbae9 :
    (Ideal.span {Xc 2 0} : Ideal (MRing (PBlk 2))) ∈ (Ideal.span {Xc 2 0} : Ideal (MRing (PBlk 2))).minimalPrimes ∧
      IsHorizontal (Ideal.span {Xc 2 0} : Ideal (MRing (PBlk 2))) ∧
      (Ideal.span {X ⟨(), 0⟩} : Ideal (MRingOver ℂ (PBlk 2))) ∈
        ((Ideal.span {Xc 2 0} : Ideal (MRing (PBlk 2))).map
          (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«DivPushMultComplex».«hyps_inhabited» := P2M_GroundTheory_Heights__Heights_Targets_DivPushMultComplex_hyps_inhabited_d7e8688bbae9
