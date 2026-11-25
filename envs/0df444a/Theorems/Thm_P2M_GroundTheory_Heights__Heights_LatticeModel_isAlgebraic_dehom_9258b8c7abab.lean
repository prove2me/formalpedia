-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_isAlgebraic_dehom_9258b8c7abab
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_isAlgebraic_dehom_9258b8c7abab
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:28:11.873301+00:00
-- url     : https://prove2.me/theorems/886d5d85-79fc-4635-9f8b-1014d1fc97fa
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model is Algebraic dehom 9258b8c7abab: P2 M Ground Theory Heights  Heights Lattice Model is Algebraic dehom 9258b8c7abab
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model is Algebraic dehom 9258b8c7abab construction uses the P2 M Ground Theory Heights  Heights Lattice Model is Algebraic dehom 9258b8c7abab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModel.lean#L71-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModel.lean#L71-L85

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

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_isAlgebraic_dehom_9258b8c7abab (u : Fin (r + 1) → K) :
    IsAlgebraic (IntermediateField.adjoin ℚ (Set.range (genericT K r))) (dehom K r (latticeForm u)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«isAlgebraic_dehom» := P2M_GroundTheory_Heights__Heights_LatticeModel_isAlgebraic_dehom_9258b8c7abab
