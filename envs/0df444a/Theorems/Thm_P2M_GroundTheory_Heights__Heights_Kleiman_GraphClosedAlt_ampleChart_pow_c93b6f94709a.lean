-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleChart_pow_c93b6f94709a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleChart_pow_c93b6f94709a
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:00:15.50256+00:00
-- url     : https://prove2.me/theorems/a68986c4-13a7-5f1e-b974-854caf47ba3a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt ample Chart pow c93b6f94709a: P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt ample Chart pow c93b6f94709a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt ample Chart pow c93b6f94709a construction uses the P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt ample Chart pow c93b6f94709a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGraphClosedLocal.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGraphClosedLocal.lean#L42-L46

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleChart_pow_c93b6f94709a (H : SubSystem S x Ω) (h : Ω) (I : Chart x) {a : Ω}
    (ha : a ∈ ampleChart H 1 h I) (e : ℕ) : a ^ e ∈ ampleChart H 1 h I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«GraphClosedAlt».«ampleChart_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleChart_pow_c93b6f94709a
