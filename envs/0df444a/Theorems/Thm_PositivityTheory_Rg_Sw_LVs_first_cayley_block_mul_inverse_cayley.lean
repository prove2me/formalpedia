-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_first_cayley_block_mul_inverse_cayley
-- name    : PositivityTheory.Rg.Sw.LVs.first_cayley_block_mul_inverse_cayley
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:45.95261+00:00
-- url     : https://prove2.me/theorems/3d15d907-7b6d-48a9-9612-1fc6cdeed40d
-- title:
--   LVs: first cayley block mul inverse cayley
-- statement:
--   The LVs construction uses the first cayley block mul inverse cayley property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulInverseCayley.lean#L44-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulInverseCayley.lean#L44-L52

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulInverseCayley
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.first_cayley_block_mul_inverse_cayley (y : M2 n) : u1 (y * Cmi n) = y.toBlocks₂₁ := by sorry
