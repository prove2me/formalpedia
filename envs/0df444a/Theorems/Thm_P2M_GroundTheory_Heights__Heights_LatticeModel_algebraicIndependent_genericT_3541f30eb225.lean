-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_algebraicIndependent_genericT_3541f30eb225
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_algebraicIndependent_genericT_3541f30eb225
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:31:36.07258+00:00
-- url     : https://prove2.me/theorems/e37ff10c-8e97-4752-9402-3225f29ecccb
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model algebraic Independent generic T 3541f30eb225: P2 M Ground Theory Heights  Heights Lattice Model algebraic Independent generic T 3541f30eb225
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model algebraic Independent generic T 3541f30eb225 construction uses the P2 M Ground Theory Heights  Heights Lattice Model algebraic Independent generic T 3541f30eb225 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModel.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModel.lean#L22-L25

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

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_algebraicIndependent_genericT_3541f30eb225 : AlgebraicIndependent ℚ (genericT K r) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«algebraicIndependent_genericT» := P2M_GroundTheory_Heights__Heights_LatticeModel_algebraicIndependent_genericT_3541f30eb225
