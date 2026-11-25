-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_suppE_4b19b1cd37eb
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_mem_suppE_4b19b1cd37eb
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:29:02.896015+00:00
-- url     : https://prove2.me/theorems/84ee9019-855f-4652-9f84-9e2491663c8a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman mem supp E 4b19b1cd37eb: P2 M Ground Theory Heights  Heights Kleiman mem supp E 4b19b1cd37eb
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman mem supp E 4b19b1cd37eb construction uses the P2 M Ground Theory Heights  Heights Kleiman mem supp E 4b19b1cd37eb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanishCone.lean#L45-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanishCone.lean#L45-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishCone
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
universe u v w
variable (S : Type u) [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
variable {S x E}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_mem_suppE_4b19b1cd37eb {w : ConeE S x E} {d : ℤ} : d ∈ suppE w ↔ coeffE S x E d w ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«mem_suppE» := P2M_GroundTheory_Heights__Heights_Kleiman_mem_suppE_4b19b1cd37eb
