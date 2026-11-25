-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_complexConjOver_apply_a73e4a8899a9
-- name    : P2M_GroundTheory_Heights__Theta_complexConjOver_apply_a73e4a8899a9
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:53:30.286127+00:00
-- url     : https://prove2.me/theorems/483e5841-c1cb-4385-86b3-525f6b46bd6f
-- title:
--   P2 M Ground Theory Heights  Theta complex Conj Over apply a73e4a8899a9: P2 M Ground Theory Heights  Theta complex Conj Over apply a73e4a8899a9
-- statement:
--   The P2 M Ground Theory Heights  Theta complex Conj Over apply a73e4a8899a9 construction uses the P2 M Ground Theory Heights  Theta complex Conj Over apply a73e4a8899a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/CMDatum.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/CMDatum.lean#L26-L28

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

theorem P2M_GroundTheory_Heights__Theta_complexConjOver_apply_a73e4a8899a9 (x : E) :
    haveI := isCMField F E
    complexConjOver F E x = IsCMField.complexConj E x := by sorry

alias «GroundTheory».«Heights₂».«Theta».«complexConjOver_apply» := P2M_GroundTheory_Heights__Theta_complexConjOver_apply_a73e4a8899a9
