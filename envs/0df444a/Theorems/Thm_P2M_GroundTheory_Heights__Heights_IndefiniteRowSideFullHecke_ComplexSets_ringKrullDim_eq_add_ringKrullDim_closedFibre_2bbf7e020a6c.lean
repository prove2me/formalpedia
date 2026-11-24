-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ringKrullDim_eq_add_ringKrullDim_closedFibre_2bbf7e020a6c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ringKrullDim_eq_add_ringKrullDim_closedFibre_2bbf7e020a6c
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:25:37.092052+00:00
-- url     : https://prove2.me/theorems/303df4cb-a4a4-43af-948b-965635ac92c8
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets ring Krull Dim eq add ring Krull Dim closed Fibre 2bbf7e020a6c: P2 M Ground Theory Heights  Heights Indefinite Row Side
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets ring Krull Dim eq add ring Krull Dim closed Fibre 2bbf7e020a6c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets ring Krull Dim eq add ring Krull Dim closed Fibre 2bbf7e020a6c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSerreRFlatAscentLocal.lean#L20-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSerreRFlatAscentLocal.lean#L20-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreConditions
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSerreRFlatAscentLocal
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
open IsLocalRing
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [IsLocalRing S]
  [IsLocalHom (algebraMap R S)]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ringKrullDim_eq_add_ringKrullDim_closedFibre_2bbf7e020a6c [IsNoetherianRing R] [IsNoetherianRing S]
    [Module.Flat R S] :
    ringKrullDim S = ringKrullDim R + ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«ringKrullDim_eq_add_ringKrullDim_closedFibre» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ringKrullDim_eq_add_ringKrullDim_closedFibre_2bbf7e020a6c
