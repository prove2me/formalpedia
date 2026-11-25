-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kleiman_coneMap_coeff_88bc714e5f8c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kleiman_coneMap_coeff_88bc714e5f8c
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:21:24.137973+00:00
-- url     : https://prove2.me/theorems/0bd0ba1a-1125-4a84-b4c2-4e18605ddc62
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kleiman cone Map coeff 88bc714e5f8c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kleiman cone Map coeff 88bc71
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kleiman cone Map coeff 88bc714e5f8c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kleiman cone Map coeff 88bc714e5f8c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CoordIdealIsMultiProjPrime.lean#L459-L469
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CoordIdealIsMultiProjPrime.lean#L459-L469

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kleiman_coneMap_coeff_88bc714e5f8c (x : σ → Ω) (f : MvPolynomial σ S) (d : ℕ) :
    (coneMap S x f).coeff d = aeval x (homogeneousComponent d f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kleiman».«coneMap_coeff» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kleiman_coneMap_coeff_88bc714e5f8c
