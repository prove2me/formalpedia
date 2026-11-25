-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_pow_twistSys_9d375c81eb90
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_pow_twistSys_9d375c81eb90
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:06:18.560147+00:00
-- url     : https://prove2.me/theorems/486e1bfb-7b2b-5fa7-885d-4547076424cb
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman pow twist Sys 9d375c81eb90: P2 M Ground Theory Heights  Heights Kleiman pow twist Sys 9d375c81eb90
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman pow twist Sys 9d375c81eb90 construction uses the P2 M Ground Theory Heights  Heights Kleiman pow twist Sys 9d375c81eb90 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistAlg.lean#L58-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistAlg.lean#L58-L68

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_pow_twistSys_9d375c81eb90 (c : ℤ) (n : ℕ) : (twistSys S x c).pow n = twistSys S x (n * c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«pow_twistSys» := P2M_GroundTheory_Heights__Heights_Kleiman_pow_twistSys_9d375c81eb90
