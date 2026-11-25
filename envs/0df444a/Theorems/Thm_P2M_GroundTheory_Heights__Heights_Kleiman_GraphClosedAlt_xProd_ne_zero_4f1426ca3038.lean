-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_xProd_ne_zero_4f1426ca3038
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_xProd_ne_zero_4f1426ca3038
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:08:31.557838+00:00
-- url     : https://prove2.me/theorems/11520279-0a4d-59cb-b57d-c22caee6746c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt x Prod ne zero 4f1426ca3038: P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt x Prod ne zero 4f1426ca3038
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt x Prod ne zero 4f1426ca3038 construction uses the P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt x Prod ne zero 4f1426ca3038 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGraphClosedLocal.lean#L51-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGraphClosedLocal.lean#L51-L52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGraphClosedLocal
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
open GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_xProd_ne_zero_4f1426ca3038 (I : Chart x) : xProd I ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«GraphClosedAlt».«xProd_ne_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_xProd_ne_zero_4f1426ca3038
