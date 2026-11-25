-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_conj_eq_complexConj_3315d27272de
-- name    : P2M_GroundTheory_Heights__Theta_conj_eq_complexConj_3315d27272de
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:53:28.27844+00:00
-- url     : https://prove2.me/theorems/f1e91834-a103-477f-b9fd-3c5daad8edaf
-- title:
--   P2 M Ground Theory Heights  Theta conj eq complex Conj 3315d27272de: P2 M Ground Theory Heights  Theta conj eq complex Conj 3315d27272de
-- statement:
--   The P2 M Ground Theory Heights  Theta conj eq complex Conj 3315d27272de construction uses the P2 M Ground Theory Heights  Theta conj eq complex Conj 3315d27272de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/CMDatum.lean#L57-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/CMDatum.lean#L57-L71

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

theorem P2M_GroundTheory_Heights__Theta_conj_eq_complexConj_3315d27272de (x : E) :
    haveI := isCMField F E
    conj F E x = IsCMField.complexConj E x := by sorry

alias «GroundTheory».«Heights₂».«Theta».«conj_eq_complexConj» := P2M_GroundTheory_Heights__Theta_conj_eq_complexConj_3315d27272de
