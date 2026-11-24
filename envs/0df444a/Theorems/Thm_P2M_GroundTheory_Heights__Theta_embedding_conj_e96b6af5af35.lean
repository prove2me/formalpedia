-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_embedding_conj_e96b6af5af35
-- name    : P2M_GroundTheory_Heights__Theta_embedding_conj_e96b6af5af35
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:28.82889+00:00
-- url     : https://prove2.me/theorems/1b7ffe67-7988-4c7f-93b0-36ef104260ef
-- title:
--   P2 M Ground Theory Heights  Theta embedding conj e96b6af5af35: P2 M Ground Theory Heights  Theta embedding conj e96b6af5af35
-- statement:
--   The P2 M Ground Theory Heights  Theta embedding conj e96b6af5af35 construction uses the P2 M Ground Theory Heights  Theta embedding conj e96b6af5af35 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/CMDatum.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/CMDatum.lean#L73-L75

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

theorem P2M_GroundTheory_Heights__Theta_embedding_conj_e96b6af5af35 (φ : E →+* ℂ) (x : E) : φ (conj F E x) = starRingEnd ℂ (φ x) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«embedding_conj» := P2M_GroundTheory_Heights__Theta_embedding_conj_e96b6af5af35
