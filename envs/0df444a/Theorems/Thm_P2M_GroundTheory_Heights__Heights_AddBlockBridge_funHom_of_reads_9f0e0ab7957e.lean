-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockBridge_funHom_of_reads_9f0e0ab7957e
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockBridge_funHom_of_reads_9f0e0ab7957e
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:18:04.839641+00:00
-- url     : https://prove2.me/theorems/8e513fcd-8aa5-4066-b074-b89630911b9c
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Bridge fun Hom of reads 9f0e0ab7957e: P2 M Ground Theory Heights  Heights Add Block Bridge fun Hom of reads 9f0e0ab7957e
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Bridge fun Hom of reads 9f0e0ab7957e construction uses the P2 M Ground Theory Heights  Heights Add Block Bridge fun Hom of reads 9f0e0ab7957e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PAddHeightsridge.lean#L116-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PAddHeightsridge.lean#L116-L134

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PAddHeightsridge
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.AddBlockBridge
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
set_option linter.unusedSectionVars false
variable (P : ArithVariety n) (y : Coord n → Ω) (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y)

theorem P2M_GroundTheory_Heights__Heights_AddBlockBridge_funHom_of_reads_9f0e0ab7957e {a : ι → ℤ} (t : IntegralSection P a) {s : Ω} (ht : P.Reads y a s t.toFun) :
    funHom P y hP t.toFun = constMap ι s * ∏ k, varT k ^ a k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockBridge».«funHom_of_reads» := P2M_GroundTheory_Heights__Heights_AddBlockBridge_funHom_of_reads_9f0e0ab7957e
