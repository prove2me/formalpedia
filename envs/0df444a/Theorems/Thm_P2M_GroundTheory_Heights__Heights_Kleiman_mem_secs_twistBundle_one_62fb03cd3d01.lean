-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_secs_twistBundle_one_62fb03cd3d01
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_mem_secs_twistBundle_one_62fb03cd3d01
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:03.536811+00:00
-- url     : https://prove2.me/theorems/7edd54a0-02c7-4538-9836-3023cd7f0dfd
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman mem secs twist Bundle one 62fb03cd3d01: P2 M Ground Theory Heights  Heights Kleiman mem secs twist Bundle one 62fb03cd3d01
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman mem secs twist Bundle one 62fb03cd3d01 construction uses the P2 M Ground Theory Heights  Heights Kleiman mem secs twist Bundle one 62fb03cd3d01 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L907-L910
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L907-L910

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_mem_secs_twistBundle_one_62fb03cd3d01 (j : Fin (N + 1)) : x j ∈ (twistBundle S x 1).secs := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«mem_secs_twistBundle_one» := P2M_GroundTheory_Heights__Heights_Kleiman_mem_secs_twistBundle_one_62fb03cd3d01
