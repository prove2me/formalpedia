-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kleiman_coneMap_monomial_a001c687d6e0
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kleiman_coneMap_monomial_a001c687d6e0
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:21:41.099069+00:00
-- url     : https://prove2.me/theorems/ed491e86-0fcf-457f-ac59-c67d1e7ed612
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kleiman cone Map monomial a001c687d6e0: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kleiman cone Map monomial
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kleiman cone Map monomial a001c687d6e0 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kleiman cone Map monomial a001c687d6e0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CoordIdealIsMultiProjPrime.lean#L452-L457
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CoordIdealIsMultiProjPrime.lean#L452-L457

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kleiman_coneMap_monomial_a001c687d6e0 (x : σ → Ω) (s : σ →₀ ℕ) (a : S) :
    coneMap S x (monomial s a) = Polynomial.C (algebraMap S Ω a * s.prod fun v e => x v ^ e) *
      Polynomial.X ^ (s.sum fun _ e => e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kleiman».«coneMap_monomial» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kleiman_coneMap_monomial_a001c687d6e0
