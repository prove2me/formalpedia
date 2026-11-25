-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_LelongWeightLimit_varInt_congr_875943a43ccc
-- name    : P2M_GroundTheory_Heights__Heights_Targets_LelongWeightLimit_varInt_congr_875943a43ccc
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:41:19.94918+00:00
-- url     : https://prove2.me/theorems/a6c91b19-aaaa-4565-82ab-a1711f45f9bb
-- title:
--   P2 M Ground Theory Heights  Heights Targets Lelong Weight Limit var Int congr 875943a43ccc: P2 M Ground Theory Heights  Heights Targets Lelong Weight Limit var Int congr 875943a43ccc
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Lelong Weight Limit var Int congr 875943a43ccc construction uses the P2 M Ground Theory Heights  Heights Targets Lelong Weight Limit var Int congr 875943a43ccc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongWeightLimit.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongWeightLimit.lean#L45-L51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLelongWeightLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLelongWeightDiff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PLelongWeightLimit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_smoothNear_of_contDiff_4853c0abca34
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_linEval_b27409562f54
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_logReg_5c8a3bcec6de
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_smoothNear_of_contDiff_8ca53b5543f3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial Filter Topology Matrix Set
open scoped ContDiff Manifold
open GroundTheory.Heights₂.Heights (varInt chartInt SmoothNear localMult linEval linForm logReg contDiff_linEval
  contDiff_logReg smoothNear_of_contDiff)
open GroundTheory.Heights₂.Heights.Targets.LelongWeightLimit
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Targets_LelongWeightLimit_varInt_congr_875943a43ccc {J : Ideal (MvPolynomial (Fin n) ℂ)} {d : ℕ} {f g : (Fin n → ℂ) → ℝ}
    (h : ∀ x ∈ ComplexSets.zeroSet J, f x = g x) (φ : Fin d → (Fin n → ℂ) → ℝ) :
    varInt J d f φ = varInt J d g φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«LelongWeightLimit».«varInt_congr» := P2M_GroundTheory_Heights__Heights_Targets_LelongWeightLimit_varInt_congr_875943a43ccc
