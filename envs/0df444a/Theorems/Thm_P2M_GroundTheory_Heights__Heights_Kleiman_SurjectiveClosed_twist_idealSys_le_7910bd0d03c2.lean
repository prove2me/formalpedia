-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_twist_idealSys_le_7910bd0d03c2
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_twist_idealSys_le_7910bd0d03c2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:21:51.549799+00:00
-- url     : https://prove2.me/theorems/ae2cf71b-d427-4486-bd4c-b3e682ead46b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Surjective Closed twist ideal Sys le 7910bd0d03c2: P2 M Ground Theory Heights  Heights Kleiman Surjective Closed twist ideal Sys le 7910bd0d03c2
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Surjective Closed twist ideal Sys le 7910bd0d03c2 construction uses the P2 M Ground Theory Heights  Heights Kleiman Surjective Closed twist ideal Sys le 7910bd0d03c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSurjectiveClosed.lean#L114-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSurjectiveClosed.lean#L114-L130

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSurjectiveClosed
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
open GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_twist_idealSys_le_7910bd0d03c2 (F : SubSystem S x Ω) (J : Ideal (Poly S N)) (I : Chart x) :
    (F.twist (idealSys x J)).sub I ≤ F.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SurjectiveClosed».«twist_idealSys_le» := P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_twist_idealSys_le_7910bd0d03c2
