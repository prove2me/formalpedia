-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kleiman_coordIdeal_isMultiProjPrime_9ec4fb651211
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kleiman_coordIdeal_isMultiProjPrime_9ec4fb651211
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:24:06.598976+00:00
-- url     : https://prove2.me/theorems/d33aaebc-4401-5521-9605-3b96998631d6
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kleiman coord Ideal is Multi Proj Prime 9ec4fb651211: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kleiman coor
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kleiman coord Ideal is Multi Proj Prime 9ec4fb651211 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kleiman coord Ideal is Multi Proj Prime 9ec4fb651211 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CoordIdealIsMultiProjPrime.lean#L473-L506
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CoordIdealIsMultiProjPrime.lean#L473-L506

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman
open MvPolynomial
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo
variable {S : Type} [CommRing S] {σ : Type} {Ω : Type} [Field Ω] [Algebra S Ω]
open GroundTheory.Heights₂.Heights.NumbersDVR

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kleiman_coordIdeal_isMultiProjPrime_9ec4fb651211 {N : ℕ} (x : Fin (N + 1) → Ω) (hx : ∃ i, x i ≠ 0) :
    IsMultiProjPrime (coordIdeal S (fun v : (Σ _ : Unit, Fin (N + 1)) => x v.2)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kleiman».«coordIdeal_isMultiProjPrime» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kleiman_coordIdeal_isMultiProjPrime_9ec4fb651211
