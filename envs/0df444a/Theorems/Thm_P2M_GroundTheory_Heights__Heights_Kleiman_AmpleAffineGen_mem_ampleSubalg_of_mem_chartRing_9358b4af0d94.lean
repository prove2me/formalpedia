-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_mem_ampleSubalg_of_mem_chartRing_9358b4af0d94
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_mem_ampleSubalg_of_mem_chartRing_9358b4af0d94
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:10:32.167867+00:00
-- url     : https://prove2.me/theorems/d6f26e56-6ab9-599a-b3a2-1fadabf1ceb2
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen mem ample Subalg of mem chart Ring 9358b4af0d94: P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen mem ample Subalg of mem chart
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen mem ample Subalg of mem chart Ring 9358b4af0d94 construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen mem ample Subalg of mem chart Ring 9358b4af0d94 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L199-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L199-L206

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_mem_ampleSubalg_of_mem_chartRing_9358b4af0d94 {H : SubSystem S x Ω} {m : ℕ} {h : Ω} {I : Chart x}
    (hh : h ∈ (H.pow m).sub I) {a : Ω} (ha : a ∈ chartRing S x I) : a ∈ ampleSubalg H m h I hh := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleAffineGen».«mem_ampleSubalg_of_mem_chartRing» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_mem_ampleSubalg_of_mem_chartRing_9358b4af0d94
