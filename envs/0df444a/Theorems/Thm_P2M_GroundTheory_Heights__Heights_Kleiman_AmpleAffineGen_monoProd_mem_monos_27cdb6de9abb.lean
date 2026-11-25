-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_monoProd_mem_monos_27cdb6de9abb
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_monoProd_mem_monos_27cdb6de9abb
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:10:35.632379+00:00
-- url     : https://prove2.me/theorems/202243d0-f193-541a-9cd2-89248a9c521c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen mono Prod mem monos 27cdb6de9abb: P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen mono Prod mem monos 27cdb6de9abb
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen mono Prod mem monos 27cdb6de9abb construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen mono Prod mem monos 27cdb6de9abb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L50-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L50-L52

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_monoProd_mem_monos_27cdb6de9abb {T I : Finset (Fin (N + 1))} (h : T ⊆ I) :
    monoProd (S := S) T ∈ monos I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleAffineGen».«monoProd_mem_monos» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_monoProd_mem_monos_27cdb6de9abb
