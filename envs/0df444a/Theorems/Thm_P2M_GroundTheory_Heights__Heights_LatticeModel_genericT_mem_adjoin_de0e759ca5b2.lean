-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_genericT_mem_adjoin_de0e759ca5b2
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_genericT_mem_adjoin_de0e759ca5b2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:28:07.088614+00:00
-- url     : https://prove2.me/theorems/514e9f5f-74ed-4927-affd-22de6141a549
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model generic T mem adjoin de0e759ca5b2: P2 M Ground Theory Heights  Heights Lattice Model generic T mem adjoin de0e759ca5b2
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model generic T mem adjoin de0e759ca5b2 construction uses the P2 M Ground Theory Heights  Heights Lattice Model generic T mem adjoin de0e759ca5b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModel.lean#L61-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModel.lean#L61-L69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.LatticeModel
variable {K : Type} [Field K] [NumberField K] {N r : ℕ} {L : Submodule (𝓞 K) (Fin (r + 1) → K)}
  {φ : Fin (N + 1) → Fin (r + 1) → K}

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_genericT_mem_adjoin_de0e759ca5b2 (hL : L.FG) (hφ : IsDualBasis L φ) (j : Fin r) :
    genericT K r j ∈ IntermediateField.adjoin ℚ (coneRatios (latticeCoord φ) fun _ : Unit ↦ (0 : Fin (N + 1))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«genericT_mem_adjoin» := P2M_GroundTheory_Heights__Heights_LatticeModel_genericT_mem_adjoin_de0e759ca5b2
