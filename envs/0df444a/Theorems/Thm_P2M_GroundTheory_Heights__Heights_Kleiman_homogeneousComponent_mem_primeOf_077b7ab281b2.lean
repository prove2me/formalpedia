-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_homogeneousComponent_mem_primeOf_077b7ab281b2
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_homogeneousComponent_mem_primeOf_077b7ab281b2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:53.732096+00:00
-- url     : https://prove2.me/theorems/2046d1aa-8a56-4102-91df-2a956641b136
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman homogeneous Component mem prime Of 077b7ab281b2: P2 M Ground Theory Heights  Heights Kleiman homogeneous Component mem prime Of 077b7ab281b2
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman homogeneous Component mem prime Of 077b7ab281b2 construction uses the P2 M Ground Theory Heights  Heights Kleiman homogeneous Component mem prime Of 077b7ab281b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L414-L416
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L414-L416

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_homogeneousComponent_mem_primeOf_077b7ab281b2 {f : Poly S N} (hf : f ∈ primeOf x) (d : ℕ) :
    homogeneousComponent d f ∈ primeOf x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«homogeneousComponent_mem_primeOf» := P2M_GroundTheory_Heights__Heights_Kleiman_homogeneousComponent_mem_primeOf_077b7ab281b2
