-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_height_add_ringKrullDim_quotient_d92c37b125a4
-- name    : P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_height_add_ringKrullDim_quotient_d92c37b125a4
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:49:14.899657+00:00
-- url     : https://prove2.me/theorems/b8362b3b-d07e-5985-b8b4-1a484bf6cbf4
-- title:
--   P2 M Ground Theory Heights  Heights Targets Base Change Min height add ring Krull Dim quotient d92c37b125a4: P2 M Ground Theory Heights  Heights Targets Base Change Min height add ring Krull Dim quoti
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Base Change Min height add ring Krull Dim quotient d92c37b125a4 construction uses the P2 M Ground Theory Heights  Heights Targets Base Change Min height add ring Krull Dim quotient d92c37b125a4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/BaseChangeMinimal.lean#L68-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/BaseChangeMinimal.lean#L68-L77

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_BaseChangeMinimal
import Theorems.Thm_ReciprocityTheory_CA_IsCM_height_add_ringKrullDim_quotient

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
open MvPolynomial
open GroundTheory.Heights₂.Heights.Targets.BaseChangeMin
variable {σ : Type*} [Fintype σ] {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']

theorem P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_height_add_ringKrullDim_quotient_d92c37b125a4 (k : Type*) [Field k]
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial σ k ⧸ P) = Fintype.card σ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«BaseChangeMin».«height_add_ringKrullDim_quotient» := P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_height_add_ringKrullDim_quotient_d92c37b125a4
