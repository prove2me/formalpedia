-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_blockAddData_joinPt_mem_39f128ebc895
-- name    : P2M_GroundTheory_Heights__Heights_blockAddData_joinPt_mem_39f128ebc895
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:40:37.213649+00:00
-- url     : https://prove2.me/theorems/e8b8b402-feba-5716-9d70-a6498285e3cd
-- title:
--   P2 M Ground Theory Heights  Heights block Add Data join Pt mem 39f128ebc895: P2 M Ground Theory Heights  Heights block Add Data join Pt mem 39f128ebc895
-- statement:
--   The P2 M Ground Theory Heights  Heights block Add Data join Pt mem 39f128ebc895 construction uses the P2 M Ground Theory Heights  Heights block Add Data join Pt mem 39f128ebc895 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L126-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L126-L140

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
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
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (n : ι → ℕ) (k₀ : ι)

theorem P2M_GroundTheory_Heights__Heights_blockAddData_joinPt_mem_39f128ebc895 (z : Cone n ℂ) (hz : BlockNonzero z) :
    (blockAddData n k₀).joinPt z (z k₀) ∈ (blockAddData n k₀).extPoints := by sorry

alias «GroundTheory».«Heights₂».«Heights».«blockAddData_joinPt_mem» := P2M_GroundTheory_Heights__Heights_blockAddData_joinPt_mem_39f128ebc895
