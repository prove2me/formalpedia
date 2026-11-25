-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_conj_ne_one_53767739c25f
-- name    : P2M_GroundTheory_Heights__Theta_conj_ne_one_53767739c25f
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:53:07.43381+00:00
-- url     : https://prove2.me/theorems/966f5052-cca2-528b-a408-aa4574bc2b08
-- title:
--   P2 M Ground Theory Heights  Theta conj ne one 53767739c25f: P2 M Ground Theory Heights  Theta conj ne one 53767739c25f
-- statement:
--   The P2 M Ground Theory Heights  Theta conj ne one 53767739c25f construction uses the P2 M Ground Theory Heights  Theta conj ne one 53767739c25f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/CMDatum.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/CMDatum.lean#L52-L55

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

theorem P2M_GroundTheory_Heights__Theta_conj_ne_one_53767739c25f : conj F E ≠ 1 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«conj_ne_one» := P2M_GroundTheory_Heights__Theta_conj_ne_one_53767739c25f
