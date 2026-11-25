-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_map_eq_of_measurePreserving_coordinates_3ae251505cbd
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_map_eq_of_measurePreserving_coordinates_3ae251505cbd
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:18:00.632132+00:00
-- url     : https://prove2.me/theorems/19156f11-f9aa-4477-86d4-aee90c914a59
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume map eq of measure Preserving coordinates 3ae251505cbd: P2 M Ground Theory Heights  Heights Finite Covolume map eq of measure Preserving coordinates
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume map eq of measure Preserving coordinates 3ae251505cbd construction uses the P2 M Ground Theory Heights  Heights Finite Covolume map eq of measure Preserving coordinates 3ae251505cbd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusHaar.lean#L29-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusHaar.lean#L29-L66

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetSqEqOneOfPreservesBilin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusHaar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory Module

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_map_eq_of_measurePreserving_coordinates_3ae251505cbd {N V : Type*} [Group N] [TopologicalSpace N]
    [IsTopologicalGroup N] [LocallyCompactSpace N] [SecondCountableTopology N] [MeasurableSpace N]
    [BorelSpace N] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] (lam : Measure V)
    [IsFiniteMeasureOnCompacts lam] [lam.IsOpenPosMeasure] (φ : V ≃ₜ N)
    (hL : ∀ n : N, MeasurePreserving (fun x => φ.symm (n * φ x)) lam lam)
    (c : N → N) (hC : MeasurePreserving (fun x => φ.symm (c (φ x))) lam lam)
    (μ : Measure N) [μ.IsHaarMeasure] : μ.map c = μ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«map_eq_of_measurePreserving_coordinates» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_map_eq_of_measurePreserving_coordinates_3ae251505cbd
