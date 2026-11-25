-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardModelDualRank_adjoin_embK_eq_span_8c48a6f16835
-- name    : P2M_GroundTheory_Heights__Heights_StandardModelDualRank_adjoin_embK_eq_span_8c48a6f16835
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:40:38.056655+00:00
-- url     : https://prove2.me/theorems/f06bf7c7-7b5c-41a2-b7f6-0dda170c4a13
-- title:
--   P2 M Ground Theory Heights  Heights Standard Model Dual Rank adjoin emb K eq span 8c48a6f16835: P2 M Ground Theory Heights  Heights Standard Model Dual Rank adjoin emb K eq span 8c48a6f16835
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Model Dual Rank adjoin emb K eq span 8c48a6f16835 construction uses the P2 M Ground Theory Heights  Heights Standard Model Dual Rank adjoin emb K eq span 8c48a6f16835 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardModelDualRank.lean#L191-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardModelDualRank.lean#L191-L206

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
variable {T : Type}

theorem P2M_GroundTheory_Heights__Heights_StandardModelDualRank_adjoin_embK_eq_span_8c48a6f16835 {n : ℕ} (B : Module.Basis (Fin n) ℚ K) (Φ₀ : Type) [Field Φ₀]
    [Algebra Φ₀ (dualStdModelField K i)] :
    Subalgebra.toSubmodule (Algebra.adjoin Φ₀ (Set.range (embK K i))) =
      Submodule.span Φ₀ (Set.range fun k => embK K i (B k)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardModelDualRank».«adjoin_embK_eq_span» := P2M_GroundTheory_Heights__Heights_StandardModelDualRank_adjoin_embK_eq_span_8c48a6f16835
