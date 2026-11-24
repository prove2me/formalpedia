-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_cone_of_isHomogeneous_046c5887f5b7
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_cone_of_isHomogeneous_046c5887f5b7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:28.673192+00:00
-- url     : https://prove2.me/theorems/24c5b4e2-9d0d-46af-90c1-d4eeefd41780
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman cone of is Homogeneous 046c5887f5b7: P2 M Ground Theory Heights  Heights Kleiman cone of is Homogeneous 046c5887f5b7
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman cone of is Homogeneous 046c5887f5b7 construction uses the P2 M Ground Theory Heights  Heights Kleiman cone of is Homogeneous 046c5887f5b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L401-L403
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L401-L403

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_cone_of_isHomogeneous_046c5887f5b7 {f : Poly S N} {d : ℕ} (hf : f.IsHomogeneous d) :
    cone x f = Polynomial.C (aeval x f) * Polynomial.X ^ d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«cone_of_isHomogeneous» := P2M_GroundTheory_Heights__Heights_Kleiman_cone_of_isHomogeneous_046c5887f5b7
