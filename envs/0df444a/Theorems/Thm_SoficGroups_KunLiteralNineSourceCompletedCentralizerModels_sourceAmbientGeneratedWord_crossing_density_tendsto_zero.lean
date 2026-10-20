-- Prove2me | Theorems.Thm_SoficGroups_KunLiteralNineSourceCompletedCentralizerModels_sourceAmbientGeneratedWord_crossing_density_tendsto_zero
-- name    : SoficGroups.KunLiteralNineSourceCompletedCentralizerModels.sourceAmbientGeneratedWord_crossing_density_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:32.70599+00:00
-- url     : https://prove2.me/theorems/844bc865-edbb-4a07-a6d4-db1655608e41
-- title:
--   SoficGroups.KunLiteralNineSourceCompletedCentralizerModels.sourceAmbientGeneratedWord_crossing_density_tendsto_zero
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunLiteralNineSourceCompletedCentralizerModels
open Filter Topology
open scoped BigOperators

theorem SoficGroups.KunLiteralNineSourceCompletedCentralizerModels.sourceAmbientGeneratedWord_crossing_density_tendsto_zero
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (S : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure
      (S : Set
        (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode)) =
          ⊤)
    (Q : ∀ n, Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (SoficGroups.boundary
            (fun i : ↥S =>
              (A.model n).action
                (i : SoficGroups.prefixElementaryGroup
                  SoficGroups.ninePrefixCode)) C : ℝ)) /
              (A.model n).size)
      atTop (𝓝 0))
    (g : SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode) :
    Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing (Q n)
          ((A.model n).action g)).card : ℝ) /
            (A.model n).size)
      atTop (𝓝 0) := by sorry
