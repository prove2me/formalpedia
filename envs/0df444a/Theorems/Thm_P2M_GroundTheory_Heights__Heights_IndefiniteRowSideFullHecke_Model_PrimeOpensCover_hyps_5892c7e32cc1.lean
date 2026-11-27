-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_PrimeOpensCover_hyps_5892c7e32cc1
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_PrimeOpensCover_hyps_5892c7e32cc1
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:24:24.834564+00:00
-- url     : https://prove2.me/theorems/10d54a83-fc90-405b-b65c-8b834032556a
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Prime Opens Cover hyps 5892c7e32cc1: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Prime Opens Cover
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Prime Opens Cover hyps 5892c7e32cc1 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Prime Opens Cover hyps 5892c7e32cc1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/IsIsoPullbackObjUnitToUnit.lean#L539-L557
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/IsIsoPullbackObjUnitToUnit.lean#L539-L557

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_WeilDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
open CategoryTheory Opposite AlgebraicGeometry Limits TopologicalSpace MonoidalCategory
open GroundTheory.Arith.SchemeCoh
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_PrimeOpensCover_hyps_5892c7e32cc1 :
    (∀ p ∈ ({prime2, prime3} : Finset Nat.Primes), ¬ (p : ℕ) ∣ 5 - (p : ℕ)) ∧
    (∀ p ∈ ({prime2, prime3} : Finset Nat.Primes), ∀ q ∈ ({prime2, prime3} : Finset Nat.Primes),
      q ≠ p → (q : ℕ) ∣ 5 - (p : ℕ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«PrimeOpensCover».«hyps» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_PrimeOpensCover_hyps_5892c7e32cc1
