-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_latticeForm_sum_41169ea91792
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_latticeForm_sum_41169ea91792
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:31:55.85187+00:00
-- url     : https://prove2.me/theorems/98c2f2de-e002-4eca-a5bd-c28852e9bf4a
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model dehom lattice Form sum 41169ea91792: P2 M Ground Theory Heights  Heights Lattice Model dehom lattice Form sum 41169ea91792
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model dehom lattice Form sum 41169ea91792 construction uses the P2 M Ground Theory Heights  Heights Lattice Model dehom lattice Form sum 41169ea91792 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModel.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModel.lean#L34-L39

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

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_latticeForm_sum_41169ea91792 (c : Fin (N + 1) → ℤ) :
    dehom K r (latticeForm (∑ b, c b • φ b)) = ∑ b, (c b : LatticeField K r) * latticeCoord φ ⟨(), b⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«dehom_latticeForm_sum» := P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_latticeForm_sum_41169ea91792
