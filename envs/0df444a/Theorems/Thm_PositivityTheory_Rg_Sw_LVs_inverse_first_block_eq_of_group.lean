-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_inverse_first_block_eq_of_group
-- name    : PositivityTheory.Rg.Sw.LVs.inverse_first_block_eq_of_group
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:26:04.147887+00:00
-- url     : https://prove2.me/theorems/2854c298-a2d7-4a52-90ab-79bac4323994
-- title:
--   LVs: inverse first block eq of group
-- statement:
--   The LVs construction uses the inverse first block eq of group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulConjTransposeEq.lean#L74-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulConjTransposeEq.lean#L74-L81

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSimpArgs false
open Matrix
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.inverse_first_block_eq_of_group {g : M2 n} (hg : InG g) : ub1 g = (u1 g)ᴴ := by sorry
