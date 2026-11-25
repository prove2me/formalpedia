-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_map_eq_smul_of_coordinates_dd57324cb110
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_map_eq_smul_of_coordinates_dd57324cb110
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:43:07.491975+00:00
-- url     : https://prove2.me/theorems/414b372e-8095-59b2-ac5e-600ebdb41c33
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume map eq smul of coordinates dd57324cb110: P2 M Ground Theory Heights  Heights Finite Covolume map eq smul of coordinates dd57324cb110
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume map eq smul of coordinates dd57324cb110 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume map eq smul of coordinates dd57324cb110 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PRadicalTorusModulus.lean#L13-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PRadicalTorusModulus.lean#L13-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PRadicalTorusModulusDet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusHaar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsRadicalTorusModulus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PRadicalTorusModulus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_map_eq_smul_of_coordinates_dd57324cb110 {N V : Type*} [Group N] [TopologicalSpace N]
    [IsTopologicalGroup N] [LocallyCompactSpace N] [SecondCountableTopology N] [MeasurableSpace N]
    [BorelSpace N] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] (lam : Measure V)
    [IsFiniteMeasureOnCompacts lam] [lam.IsOpenPosMeasure] (φ : V ≃ₜ N)
    (hL : ∀ n : N, MeasurePreserving (fun x => φ.symm (n * φ x)) lam lam)
    (T : V → V) (hT : Measurable T) (k : ℝ≥0∞) (hC : lam.map T = k • lam)
    (μ : Measure N) [μ.IsHaarMeasure] : μ.map (φ ∘ T ∘ φ.symm) = k • μ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«map_eq_smul_of_coordinates» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_map_eq_smul_of_coordinates_dd57324cb110
