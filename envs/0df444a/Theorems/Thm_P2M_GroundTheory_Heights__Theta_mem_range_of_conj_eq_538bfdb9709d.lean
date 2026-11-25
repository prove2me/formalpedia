-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_mem_range_of_conj_eq_538bfdb9709d
-- name    : P2M_GroundTheory_Heights__Theta_mem_range_of_conj_eq_538bfdb9709d
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:54:14.996098+00:00
-- url     : https://prove2.me/theorems/18300bb0-d378-40d0-a8d8-962095e9e799
-- title:
--   P2 M Ground Theory Heights  Theta mem range of conj eq 538bfdb9709d: P2 M Ground Theory Heights  Theta mem range of conj eq 538bfdb9709d
-- statement:
--   The P2 M Ground Theory Heights  Theta mem range of conj eq 538bfdb9709d construction uses the P2 M Ground Theory Heights  Theta mem range of conj eq 538bfdb9709d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/CMDatum.lean#L41-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/CMDatum.lean#L41-L48

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

theorem P2M_GroundTheory_Heights__Theta_mem_range_of_conj_eq_538bfdb9709d {x : E} (hx : conj F E x = x) :
    x ∈ Set.range (algebraMap F E) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«mem_range_of_conj_eq» := P2M_GroundTheory_Heights__Theta_mem_range_of_conj_eq_538bfdb9709d
