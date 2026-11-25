-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_scalar_section_mul_block_unipotent
-- name    : PositivityTheory.Rg.Sw.LVs.scalar_section_mul_block_unipotent
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:01:10.636047+00:00
-- url     : https://prove2.me/theorems/24b0dd34-fb6a-5f97-84ee-6c465c9f02e0
-- title:
--   LVs: scalar section mul block unipotent
-- statement:
--   The LVs construction uses the scalar section mul block unipotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulInverseCayley.lean#L132-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulInverseCayley.lean#L132-L152

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

theorem PositivityTheory.Rg.Sw.LVs.scalar_section_mul_block_unipotent {p q : ℤ} {j : ℕ} {x : M2 n} (h1 : (u1 x).det ≠ 0) (h2 : (u2 x).det ≠ 0)
    (T : Matrix (blkA (n := n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ) :
    f0 p q (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1) =
      (f0 p q x * (1 + subOn (blkA j) (wM x) * T).det ^ (-q)) *
        (1 + subOn (blkB j) (wM x)⁻¹ * S).det ^ (-p) := by sorry
