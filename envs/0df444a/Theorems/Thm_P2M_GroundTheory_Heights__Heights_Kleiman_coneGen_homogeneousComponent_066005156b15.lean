-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coneGen_homogeneousComponent_066005156b15
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_coneGen_homogeneousComponent_066005156b15
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:11.830823+00:00
-- url     : https://prove2.me/theorems/d355baa1-e845-4366-80f0-b0f8888cf012
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman cone Gen homogeneous Component 066005156b15: P2 M Ground Theory Heights  Heights Kleiman cone Gen homogeneous Component 066005156b15
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman cone Gen homogeneous Component 066005156b15 construction uses the P2 M Ground Theory Heights  Heights Kleiman cone Gen homogeneous Component 066005156b15 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L368-L383
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L368-L383

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_coneGen_homogeneousComponent_066005156b15 {σ : Type*} (y : σ → Ω) {g : MvPolynomial σ S}
    (hg : coneGen y g = 0) (d : ℕ) : coneGen y (homogeneousComponent d g) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«coneGen_homogeneousComponent» := P2M_GroundTheory_Heights__Heights_Kleiman_coneGen_homogeneousComponent_066005156b15
