-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUp_relation_be19b3539eff
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUp_relation_be19b3539eff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:32.846562+00:00
-- url     : https://prove2.me/theorems/7858b770-3c81-40f7-91c2-cd9472d76292
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR blow Up relation be19b3539eff: P2 M Ground Theory Heights  Heights Numbers DVR blow Up relation be19b3539eff
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR blow Up relation be19b3539eff construction uses the P2 M Ground Theory Heights  Heights Numbers DVR blow Up relation be19b3539eff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CutIdentityRightSideCongrOfSubMem.lean#L296-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CutIdentityRightSideCongrOfSubMem.lean#L296-L302

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_SpanTwoIsPrimeRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
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
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUp_relation_be19b3539eff {K : Type} [Fintype K] {ι : K → Type} {R : Type*} [CommRing R]
    (P : Ideal (MRing ι R)) (s g f m : MRing ι R) (e : K → ℕ) :
    liftForm (s * g) * newVar (some none) - liftForm (f * m) * newVar none ∈
      blowUpOf P (blowUpGens s g f m e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«blowUp_relation» := P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUp_relation_be19b3539eff
