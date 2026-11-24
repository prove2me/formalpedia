-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:35.780946+00:00
-- url     : https://prove2.me/theorems/9925e173-1202-4d44-8e3c-541b0e43cd97
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman mem prime Of of is Homogeneous ce26327b239d: P2 M Ground Theory Heights  Heights Kleiman mem prime Of of is Homogeneous ce26327b239d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman mem prime Of of is Homogeneous ce26327b239d construction uses the P2 M Ground Theory Heights  Heights Kleiman mem prime Of of is Homogeneous ce26327b239d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L405-L412
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L405-L412

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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω]
variable {N : ℕ} (x : Fin (N + 1) → Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d {f : Poly S N} {d : ℕ} (hf : f.IsHomogeneous d) :
    f ∈ primeOf x ↔ aeval x f = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«mem_primeOf_of_isHomogeneous» := P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d
