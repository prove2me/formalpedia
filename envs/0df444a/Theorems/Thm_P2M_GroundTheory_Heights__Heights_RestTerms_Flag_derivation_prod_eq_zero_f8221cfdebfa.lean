-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_derivation_prod_eq_zero_f8221cfdebfa
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_derivation_prod_eq_zero_f8221cfdebfa
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:48.98596+00:00
-- url     : https://prove2.me/theorems/6b1bece5-8ab1-4b87-9236-85261275bbc1
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag derivation prod eq zero f8221cfdebfa: P2 M Ground Theory Heights  Heights Rest Terms Flag derivation prod eq zero f8221cfdebfa
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag derivation prod eq zero f8221cfdebfa construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag derivation prod eq zero f8221cfdebfa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L30-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L30-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_derivation_prod_eq_zero_f8221cfdebfa {R A M : Type*} [CommSemiring R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] [Module R M] (D : Derivation R A M) {ι : Type*} (s : Finset ι) (g : ι → A) (hg : ∀ i ∈ s, D (g i) = 0) :
    D (∏ i ∈ s, g i) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«derivation_prod_eq_zero» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_derivation_prod_eq_zero_f8221cfdebfa
