-- Prove2me | Theorems.Thm_SoficGroups_KunActualBothTransportedOverlapScales_source_both_transported_generator_boundary_density_tendsto_zero
-- name    : SoficGroups.KunActualBothTransportedOverlapScales.source_both_transported_generator_boundary_density_tendsto_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:32.70599+00:00
-- url     : https://prove2.me/theorems/353ce795-c89f-46d6-b7b5-efd1f5e269e6
-- title:
--   SoficGroups.KunActualBothTransportedOverlapScales.source_both_transported_generator_boundary_density_tendsto_zero
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualBothTransportedOverlapScales
open Filter Topology
open scoped BigOperators

theorem SoficGroups.KunActualBothTransportedOverlapScales.source_both_transported_generator_boundary_density_tendsto_zero
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (S : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure
      (S : Set
        (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode)) =
          ⊤)
    (Q : ∀ n, Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    (hsource : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (SoficGroups.boundary
            (fun i : ↥S =>
              (A.model n).action
                (SoficGroups.SourceBothCompressionNormalization.sourceAlphaElement
                  (i : SoficGroups.prefixElementaryGroup
                    SoficGroups.alphaPrefixCode))) C : ℝ)) /
              (A.model n).size)
      atTop (nhds 0)) :
    ∀ j : Fin 2, Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (SoficGroups.boundary
            (fun i : ↥S =>
              (A.model n).action
                  (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j) *
                (A.model n).action
                  (SoficGroups.SourceBothCompressionNormalization.sourceAlphaElement
                    (i : SoficGroups.prefixElementaryGroup
                      SoficGroups.alphaPrefixCode)) *
                ((A.model n).action
                  (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j))⁻¹)
            C : ℝ)) /
              (A.model n).size)
      atTop (nhds 0) := by sorry
