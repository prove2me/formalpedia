-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_span_range_eq_twistMod_one_cf9eb67143e0
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_span_range_eq_twistMod_one_cf9eb67143e0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:55.11211+00:00
-- url     : https://prove2.me/theorems/142b81ca-25c9-4939-8692-6a8aab965d9a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman span range eq twist Mod one cf9eb67143e0: P2 M Ground Theory Heights  Heights Kleiman span range eq twist Mod one cf9eb67143e0
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman span range eq twist Mod one cf9eb67143e0 construction uses the P2 M Ground Theory Heights  Heights Kleiman span range eq twist Mod one cf9eb67143e0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L897-L905
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L897-L905

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_span_range_eq_twistMod_one_cf9eb67143e0 (I : Chart x) :
    Submodule.span (chartRing S x I) (Set.range x) = twistMod S x 1 I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«span_range_eq_twistMod_one» := P2M_GroundTheory_Heights__Heights_Kleiman_span_range_eq_twistMod_one_cf9eb67143e0
