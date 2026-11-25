-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockData_chartMonomial_mem_of_not_isLive_a21aa707419f
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockData_chartMonomial_mem_of_not_isLive_a21aa707419f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:15:17.147989+00:00
-- url     : https://prove2.me/theorems/7604ab7c-5cd3-4d3b-b9d6-aaa9d18e8dd2
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Data chart Monomial mem of not is Live a21aa707419f: P2 M Ground Theory Heights  Heights Add Block Data chart Monomial mem of not is Live a21aa707419f
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Data chart Monomial mem of not is Live a21aa707419f construction uses the P2 M Ground Theory Heights  Heights Add Block Data chart Monomial mem of not is Live a21aa707419f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ExtMapLiftOldOfIsWeightedHomogeneous.lean#L63-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ExtMapLiftOldOfIsWeightedHomogeneous.lean#L63-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ExtMapLiftOldOfIsWeightedHomogeneous
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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.AddBlockData
variable {P : ArithVariety n} (D : AddBlockData P)

theorem P2M_GroundTheory_Heights__Heights_AddBlockData_chartMonomial_mem_of_not_isLive_a21aa707419f {c : (k : ι) → Fin (n k + 1)} (hc : ¬ P.IsLive c)
    {d : ι → ℕ} (hd : ∀ k, 1 ≤ d k) : chartMonomial c d ∈ P.ideal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockData».«chartMonomial_mem_of_not_isLive» := P2M_GroundTheory_Heights__Heights_AddBlockData_chartMonomial_mem_of_not_isLive_a21aa707419f
