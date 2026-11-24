-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coneGen_of_isHomogeneous_d90e26b2f3c5
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_coneGen_of_isHomogeneous_d90e26b2f3c5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:22.317483+00:00
-- url     : https://prove2.me/theorems/f99cb8ce-68c7-4fcf-97de-8cd6950bdad5
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman cone Gen of is Homogeneous d90e26b2f3c5: P2 M Ground Theory Heights  Heights Kleiman cone Gen of is Homogeneous d90e26b2f3c5
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman cone Gen of is Homogeneous d90e26b2f3c5 construction uses the P2 M Ground Theory Heights  Heights Kleiman cone Gen of is Homogeneous d90e26b2f3c5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L353-L366
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L353-L366

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_coneGen_of_isHomogeneous_d90e26b2f3c5 {σ : Type*} (y : σ → Ω) {g : MvPolynomial σ S} {d : ℕ}
    (hg : g.IsHomogeneous d) : coneGen y g = Polynomial.C (aeval y g) * Polynomial.X ^ d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«coneGen_of_isHomogeneous» := P2M_GroundTheory_Heights__Heights_Kleiman_coneGen_of_isHomogeneous_d90e26b2f3c5
