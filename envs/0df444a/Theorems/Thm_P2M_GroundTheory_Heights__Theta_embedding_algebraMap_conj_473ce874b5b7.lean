-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_embedding_algebraMap_conj_473ce874b5b7
-- name    : P2M_GroundTheory_Heights__Theta_embedding_algebraMap_conj_473ce874b5b7
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:24.685645+00:00
-- url     : https://prove2.me/theorems/47835967-0793-40d3-b92e-ec16067eabd5
-- title:
--   P2 M Ground Theory Heights  Theta embedding algebra Map conj 473ce874b5b7: P2 M Ground Theory Heights  Theta embedding algebra Map conj 473ce874b5b7
-- statement:
--   The P2 M Ground Theory Heights  Theta embedding algebra Map conj 473ce874b5b7 construction uses the P2 M Ground Theory Heights  Theta embedding algebra Map conj 473ce874b5b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/CMDatum.lean#L77-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/CMDatum.lean#L77-L79

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_CMDatum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open NumberField GroundTheory.Automorphic
variable (F E : Type*) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
  [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {F E}
variable (F E)

theorem P2M_GroundTheory_Heights__Theta_embedding_algebraMap_conj_473ce874b5b7 (φ : E →+* ℂ) (c : F) :
    starRingEnd ℂ (φ (algebraMap F E c)) = φ (algebraMap F E c) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«embedding_algebraMap_conj» := P2M_GroundTheory_Heights__Theta_embedding_algebraMap_conj_473ce874b5b7
