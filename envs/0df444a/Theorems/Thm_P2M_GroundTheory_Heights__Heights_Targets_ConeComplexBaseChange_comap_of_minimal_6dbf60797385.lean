-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ConeComplexBaseChange_comap_of_minimal_6dbf60797385
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ConeComplexBaseChange_comap_of_minimal_6dbf60797385
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:43:11.628135+00:00
-- url     : https://prove2.me/theorems/b371e571-6812-5711-a3cb-9f56039a0a2e
-- title:
--   P2 M Ground Theory Heights  Heights Targets Cone Complex Base Change comap of minimal 6dbf60797385: P2 M Ground Theory Heights  Heights Targets Cone Complex Base Change comap of minimal 6dbf60797385
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Cone Complex Base Change comap of minimal 6dbf60797385 construction uses the P2 M Ground Theory Heights  Heights Targets Cone Complex Base Change comap of minimal 6dbf60797385 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PConeComplexBaseChange.lean#L24-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PConeComplexBaseChange.lean#L24-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsConeComplexBaseChange
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PConeComplexBaseChange
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
open GroundTheory.Heights₂.Heights.Targets.ConeComplexBaseChange
variable {σ : Type} [Fintype σ]

theorem P2M_GroundTheory_Heights__Heights_Targets_ConeComplexBaseChange_comap_of_minimal_6dbf60797385 (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime]
    (hP : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥) (Q : Ideal (MvPolynomial σ ℂ))
    (hQ : Q ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) :
    Q.comap (MvPolynomial.map (Int.castRingHom ℂ)) = P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ConeComplexBaseChange».«comap_of_minimal» := P2M_GroundTheory_Heights__Heights_Targets_ConeComplexBaseChange_comap_of_minimal_6dbf60797385
