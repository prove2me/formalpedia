-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_chartRatio_mem_da6fc1cf715f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_chartRatio_mem_da6fc1cf715f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:10:57.434821+00:00
-- url     : https://prove2.me/theorems/fd70d4cb-e16b-4e2f-8657-5cc4ea4ab247
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen chart Ratio mem da6fc1cf715f: P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen chart Ratio mem da6fc1cf715f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen chart Ratio mem da6fc1cf715f construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen chart Ratio mem da6fc1cf715f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L58-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L58-L62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
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
open GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_chartRatio_mem_da6fc1cf715f (I J : Chart x) : chartRatio I J ∈ chartRing S x I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleAffineGen».«chartRatio_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_chartRatio_mem_da6fc1cf715f
