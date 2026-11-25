-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistSys_sub_mul_ed3d7223ab6a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_twistSys_sub_mul_ed3d7223ab6a
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:07:58.725425+00:00
-- url     : https://prove2.me/theorems/64af8189-fe92-4526-a734-ed31eb9189d6
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman twist Sys sub mul ed3d7223ab6a: P2 M Ground Theory Heights  Heights Kleiman twist Sys sub mul ed3d7223ab6a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman twist Sys sub mul ed3d7223ab6a construction uses the P2 M Ground Theory Heights  Heights Kleiman twist Sys sub mul ed3d7223ab6a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistAlg.lean#L74-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistAlg.lean#L74-L76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_twistSys_sub_mul_ed3d7223ab6a (a b : ℤ) (I : Chart x) :
    (twistSys S x a).sub I * (twistSys S x b).sub I = (twistSys S x (a + b)).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«twistSys_sub_mul» := P2M_GroundTheory_Heights__Heights_Kleiman_twistSys_sub_mul_ed3d7223ab6a
