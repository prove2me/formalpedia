-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardModelDualRank_indep_int_3d1823af2d86
-- name    : P2M_GroundTheory_Heights__Heights_StandardModelDualRank_indep_int_3d1823af2d86
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:39:44.429404+00:00
-- url     : https://prove2.me/theorems/e167ee19-d5f3-4b91-aa77-ab81f898c7ce
-- title:
--   P2 M Ground Theory Heights  Heights Standard Model Dual Rank indep int 3d1823af2d86: P2 M Ground Theory Heights  Heights Standard Model Dual Rank indep int 3d1823af2d86
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Model Dual Rank indep int 3d1823af2d86 construction uses the P2 M Ground Theory Heights  Heights Standard Model Dual Rank indep int 3d1823af2d86 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardModelDualRank.lean#L84-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardModelDualRank.lean#L84-L97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardModelDualRank
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField DualArithmeticVariety
noncomputable section
open GroundTheory.Heights₂.Heights.StandardModelDualRank
variable {K : Type} [Field K] {i : ℕ}
variable [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_StandardModelDualRank_indep_int_3d1823af2d86 {n : ℕ} (B : Module.Basis (Fin n) ℚ K) (q : Fin n → MvPolynomial (Fin i) ℤ)
    (h : ∑ k, embK K i (B k) * psiZ K i (q k) = 0) : ∀ k, q k = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardModelDualRank».«indep_int» := P2M_GroundTheory_Heights__Heights_StandardModelDualRank_indep_int_3d1823af2d86
