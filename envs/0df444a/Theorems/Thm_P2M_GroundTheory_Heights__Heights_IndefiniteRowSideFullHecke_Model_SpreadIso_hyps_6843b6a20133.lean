-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_SpreadIso_hyps_6843b6a20133
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_SpreadIso_hyps_6843b6a20133
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:24:27.500001+00:00
-- url     : https://prove2.me/theorems/94a2208e-47b5-53ea-baf3-1b3aec5754ca
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Spread Iso hyps 6843b6a20133: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Spread Iso hyps 6843b6a2
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Spread Iso hyps 6843b6a20133 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Spread Iso hyps 6843b6a20133 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/IsIsoPullbackObjUnitToUnit.lean#L533-L537
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/IsIsoPullbackObjUnitToUnit.lean#L533-L537

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_SpreadIso_hyps_6843b6a20133 :
    IsFiniteTypeOverZ specInt ∧ 0 < 2 ∧ IsVectorBundle (𝟙_ (invOpen specInt 2).toScheme.Modules) ∧
    Nonempty ((Scheme.Modules.pullback (genRes specInt 2)).obj (𝟙_ (invOpen specInt 2).toScheme.Modules) ≅
      (Scheme.Modules.pullback (genRes specInt 2)).obj (𝟙_ (invOpen specInt 2).toScheme.Modules)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«SpreadIso».«hyps» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_SpreadIso_hyps_6843b6a20133
