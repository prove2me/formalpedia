-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistSys_twist_eq_add_659a52088064
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_twistSys_twist_eq_add_659a52088064
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:06:52.604424+00:00
-- url     : https://prove2.me/theorems/2acc0a5b-feb5-491e-91ca-17a3d56fc025
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman twist Sys twist eq add 659a52088064: P2 M Ground Theory Heights  Heights Kleiman twist Sys twist eq add 659a52088064
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman twist Sys twist eq add 659a52088064 construction uses the P2 M Ground Theory Heights  Heights Kleiman twist Sys twist eq add 659a52088064 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistAlg.lean#L48-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistAlg.lean#L48-L56

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_twistSys_twist_eq_add_659a52088064 (a b : ℤ) :
    (twistSys S x a).twist (twistSys S x b) = twistSys S x (a + b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«twistSys_twist_eq_add» := P2M_GroundTheory_Heights__Heights_Kleiman_twistSys_twist_eq_add_659a52088064
