-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_exists_bound_pairs_7ea5a7f18a7c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_exists_bound_pairs_7ea5a7f18a7c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:42.799054+00:00
-- url     : https://prove2.me/theorems/02d07594-aa34-4869-b064-a5a512b2b2e3
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Fibre Discriminant Holomorphic exists bound pairs 7ea5a7f18a7c: P2 M Ground Theory Heights  Heights Indefinite Row Side
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Fibre Discriminant Holomorphic exists bound pairs 7ea5a7f18a7c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Fibre Discriminant Holomorphic exists bound pairs 7ea5a7f18a7c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFibreDiscriminantHolomorphic.lean#L91-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFibreDiscriminantHolomorphic.lean#L91-L101

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
omit [Fintype σ]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_exists_bound_pairs_7ea5a7f18a7c {Y : Set (σ → ℂ)} {d : ℕ} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)}
    {K : Set (Fin d → ℂ)} (l : (σ → ℂ) →L[ℂ] ℂ) (hK : IsCompact {x | x ∈ Y ∧ A x ∈ K}) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a ∈ {x | x ∈ Y ∧ A x ∈ K}, ∀ b ∈ {x | x ∈ Y ∧ A x ∈ K}, ‖l a - l b‖ ≤ C := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«FibreDiscriminantHolomorphic».«exists_bound_pairs» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_exists_bound_pairs_7ea5a7f18a7c
