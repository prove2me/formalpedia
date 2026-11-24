-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_norm_prod_le_pow_309320c6e6da
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_norm_prod_le_pow_309320c6e6da
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:21.322796+00:00
-- url     : https://prove2.me/theorems/72225d76-19c7-457b-b895-6224997803e6
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Fibre Discriminant Holomorphic norm prod le pow 309320c6e6da: P2 M Ground Theory Heights  Heights Indefinite Row Side Fu
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Fibre Discriminant Holomorphic norm prod le pow 309320c6e6da construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Fibre Discriminant Holomorphic norm prod le pow 309320c6e6da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFibreDiscriminantHolomorphic.lean#L82-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFibreDiscriminantHolomorphic.lean#L82-L87

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFibreDiscriminantHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreDiscriminantHolomorphic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Metric Set
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreDiscriminantHolomorphic
variable {σ : Type} [Fintype σ]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_norm_prod_le_pow_309320c6e6da {ι : Type*} (s : Finset ι) (F : ι → ℂ) {C : ℝ} (hC : 1 ≤ C) {n : ℕ}
    (hs : s.card ≤ n) (hF : ∀ i ∈ s, ‖F i‖ ≤ C) : ‖∏ i ∈ s, F i‖ ≤ C ^ n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«FibreDiscriminantHolomorphic».«norm_prod_le_pow» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_norm_prod_le_pow_309320c6e6da
