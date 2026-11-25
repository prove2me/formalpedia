-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_bound_metricDefect_474cdf5ff6c9
-- name    : P2M_GroundTheory_Heights__Heights_exists_bound_metricDefect_474cdf5ff6c9
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:45:44.398748+00:00
-- url     : https://prove2.me/theorems/ba53369a-c95a-53e1-bd07-9f467bb10e46
-- title:
--   P2 M Ground Theory Heights  Heights exists bound metric Defect 474cdf5ff6c9: P2 M Ground Theory Heights  Heights exists bound metric Defect 474cdf5ff6c9
-- statement:
--   The P2 M Ground Theory Heights  Heights exists bound metric Defect 474cdf5ff6c9 construction uses the P2 M Ground Theory Heights  Heights exists bound metric Defect 474cdf5ff6c9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Comparison.lean#L58-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Comparison.lean#L58-L82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_exists_bound_metricDefect_474cdf5ff6c9 (A : HermLine n) :
    ∃ M, ∀ z : Cone n ℂ, BlockNonzero z → |metricDefect A z| ≤ M := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_bound_metricDefect» := P2M_GroundTheory_Heights__Heights_exists_bound_metricDefect_474cdf5ff6c9
