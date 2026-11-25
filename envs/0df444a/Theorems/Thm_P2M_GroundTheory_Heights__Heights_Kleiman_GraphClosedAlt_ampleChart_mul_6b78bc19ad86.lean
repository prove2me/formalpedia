-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleChart_mul_6b78bc19ad86
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleChart_mul_6b78bc19ad86
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:05:49.414381+00:00
-- url     : https://prove2.me/theorems/96b93302-e32b-5605-910d-8edc8dd7a005
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt ample Chart mul 6b78bc19ad86: P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt ample Chart mul 6b78bc19ad86
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt ample Chart mul 6b78bc19ad86 construction uses the P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt ample Chart mul 6b78bc19ad86 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGraphClosedLocal.lean#L30-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGraphClosedLocal.lean#L30-L40

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleChart_mul_6b78bc19ad86 (H : SubSystem S x Ω) (h : Ω) (I : Chart x) {a b : Ω}
    (ha : a ∈ ampleChart H 1 h I) (hb : b ∈ ampleChart H 1 h I) : a * b ∈ ampleChart H 1 h I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«GraphClosedAlt».«ampleChart_mul» := P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleChart_mul_6b78bc19ad86
