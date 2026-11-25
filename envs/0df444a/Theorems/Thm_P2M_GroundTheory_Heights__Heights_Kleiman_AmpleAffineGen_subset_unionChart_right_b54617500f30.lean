-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_subset_unionChart_right_b54617500f30
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_subset_unionChart_right_b54617500f30
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:12:22.344354+00:00
-- url     : https://prove2.me/theorems/0f6df907-dd1f-4571-ad02-ca351944c13a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen subset union Chart right b54617500f30: P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen subset union Chart right b54617500f30
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen subset union Chart right b54617500f30 construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen subset union Chart right b54617500f30 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L25-L26

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_subset_unionChart_right_b54617500f30 (I J : Chart x) : J.1 ⊆ (unionChart I J).1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleAffineGen».«subset_unionChart_right» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_subset_unionChart_right_b54617500f30
