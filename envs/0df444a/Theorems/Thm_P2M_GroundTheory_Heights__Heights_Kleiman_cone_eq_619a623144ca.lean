-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_cone_eq_619a623144ca
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_cone_eq_619a623144ca
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:45.319171+00:00
-- url     : https://prove2.me/theorems/c30d9951-5c1c-439e-8d3b-88b0f282b540
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman cone eq 619a623144ca: P2 M Ground Theory Heights  Heights Kleiman cone eq 619a623144ca
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman cone eq 619a623144ca construction uses the P2 M Ground Theory Heights  Heights Kleiman cone eq 619a623144ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L389-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L389-L389

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_cone_eq_619a623144ca : cone (S := S) x = coneGen x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«cone_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_cone_eq_619a623144ca
