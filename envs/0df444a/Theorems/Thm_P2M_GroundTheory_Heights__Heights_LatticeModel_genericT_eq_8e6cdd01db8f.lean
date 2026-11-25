-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_genericT_eq_8e6cdd01db8f
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_genericT_eq_8e6cdd01db8f
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:28:57.9378+00:00
-- url     : https://prove2.me/theorems/4fda80cc-59c1-4cf6-afb4-8083c03e53af
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model generic T eq 8e6cdd01db8f: P2 M Ground Theory Heights  Heights Lattice Model generic T eq 8e6cdd01db8f
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model generic T eq 8e6cdd01db8f construction uses the P2 M Ground Theory Heights  Heights Lattice Model generic T eq 8e6cdd01db8f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModel.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModel.lean#L27-L28

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

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_genericT_eq_8e6cdd01db8f (j : Fin r) : genericT K r j = dehom K r (latticeForm (Pi.single j.succ 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«genericT_eq» := P2M_GroundTheory_Heights__Heights_LatticeModel_genericT_eq_8e6cdd01db8f
