-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mem_smul_top_iff_mem_map_smul_top_4aa33f369c61
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mem_smul_top_iff_mem_map_smul_top_4aa33f369c61
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:02.147169+00:00
-- url     : https://prove2.me/theorems/9cfd6e56-3068-48e2-ba70-57b3c2e5a91a
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets mem smul top iff mem map smul top 4aa33f369c61: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Compl
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets mem smul top iff mem map smul top 4aa33f369c61 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets mem smul top iff mem map smul top 4aa33f369c61 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFlatLocalRegularElement.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFlatLocalRegularElement.lean#L66-L69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatLocalRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFlatLocalRegularElement
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
open IsLocalRing TensorProduct
open scoped Pointwise
variable {A B M : Type} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mem_smul_top_iff_mem_map_smul_top_4aa33f369c61 (I : Ideal A) (x : M) :
    x ∈ I • (⊤ : Submodule A M) ↔ x ∈ I.map (algebraMap A B) • (⊤ : Submodule B M) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«mem_smul_top_iff_mem_map_smul_top» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mem_smul_top_iff_mem_map_smul_top_4aa33f369c61
