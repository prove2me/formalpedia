-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_intNum_comp_perm_d3826893cbaa
-- name    : P2M_GroundTheory_Heights__Heights_Targets_intNum_comp_perm_d3826893cbaa
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:45:56.861904+00:00
-- url     : https://prove2.me/theorems/3121b0bb-fd57-5079-9042-eb3ddb58e78a
-- title:
--   P2 M Ground Theory Heights  Heights Targets int Num comp perm d3826893cbaa: P2 M Ground Theory Heights  Heights Targets int Num comp perm d3826893cbaa
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets int Num comp perm d3826893cbaa construction uses the P2 M Ground Theory Heights  Heights Targets int Num comp perm d3826893cbaa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/IntNumCompPerm.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/IntNumCompPerm.lean#L14-L18

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsFieldIntersectionExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsSymmRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_IntNumCompPerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.NumbersDVR
universe u v w

theorem P2M_GroundTheory_Heights__Heights_Targets_intNum_comp_perm_d3826893cbaa {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
    (P : Ideal (MRing ι F)) {n : ℕ} (bs : Fin n → K → ℤ) (σ : Equiv.Perm (Fin n)) :
    intNum F P (bs ∘ σ) = intNum F P bs := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«intNum_comp_perm» := P2M_GroundTheory_Heights__Heights_Targets_intNum_comp_perm_d3826893cbaa
