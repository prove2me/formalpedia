-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_assoc_e501c3cc2859
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_assoc_e501c3cc2859
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:06:41.192081+00:00
-- url     : https://prove2.me/theorems/7bd15349-17db-452f-9dd8-44ae9b8b31a8
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sub System twist assoc e501c3cc2859: P2 M Ground Theory Heights  Heights Kleiman Sub System twist assoc e501c3cc2859
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sub System twist assoc e501c3cc2859 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sub System twist assoc e501c3cc2859 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistAlg.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistAlg.lean#L33-L34

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
open GroundTheory.Heights₂.Heights.Kleiman.SubSystem

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_assoc_e501c3cc2859 (F P Q : SubSystem S x Ω) : (F.twist P).twist Q = F.twist (P.twist Q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SubSystem».«twist_assoc» := P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_assoc_e501c3cc2859
