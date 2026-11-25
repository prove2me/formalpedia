-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_DominatingDVR_hyps_52de9d255732
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_DominatingDVR_hyps_52de9d255732
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:24:25.640102+00:00
-- url     : https://prove2.me/theorems/4e84018e-7f83-4f96-9ebd-539aa351a3c7
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Dominating DVR hyps 52de9d255732: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Dominating DVR hyps
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Dominating DVR hyps 52de9d255732 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Dominating DVR hyps 52de9d255732 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/IsIsoPullbackObjUnitToUnit.lean#L434-L440
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/IsIsoPullbackObjUnitToUnit.lean#L434-L440

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_DominatingDVR_hyps_52de9d255732 :
    (IsDomain ℤ_[2] ∧ IsLocalRing ℤ_[2] ∧ IsNoetherianRing ℤ_[2] ∧ IsFractionRing ℤ_[2] ℚ_[2] ∧
      ¬ IsField ℤ_[2]) ∧
    (IsIntegral specInt ∧ IsLocallyNoetherian specInt ∧ closedPt prime2 ≠ genericPoint specInt) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«DominatingDVR».«hyps» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_DominatingDVR_hyps_52de9d255732
