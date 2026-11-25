-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_KrullAkizuki_hyps_6317c92547c3
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_KrullAkizuki_hyps_6317c92547c3
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:24:18.86665+00:00
-- url     : https://prove2.me/theorems/5c6648db-eefc-5358-8665-95de3b39bab3
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Krull Akizuki hyps 6317c92547c3: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Krull Akizuki hyps 63
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Krull Akizuki hyps 6317c92547c3 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Krull Akizuki hyps 6317c92547c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/IsIsoPullbackObjUnitToUnit.lean#L450-L454
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/IsIsoPullbackObjUnitToUnit.lean#L450-L454

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_KrullAkizuki_hyps_6317c92547c3 :
    IsNoetherianRing ℤ ∧ IsFractionRing ℤ ℚ ∧ FiniteDimensional ℚ ℚ ∧ IsScalarTower ℤ ℚ ℚ ∧
      ringKrullDim ℤ = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«KrullAkizuki».«hyps» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_KrullAkizuki_hyps_6317c92547c3
