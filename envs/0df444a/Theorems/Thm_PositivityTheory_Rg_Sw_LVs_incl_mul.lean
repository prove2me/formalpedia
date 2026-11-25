-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_incl_mul
-- name    : PositivityTheory.Rg.Sw.LVs.incl_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:03:05.476477+00:00
-- url     : https://prove2.me/theorems/45b64d67-6311-5cbb-948b-0d7b36344290
-- title:
--   LVs: incl mul
-- statement:
--   The LVs construction uses the incl mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulInverseCayley.lean#L99-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulInverseCayley.lean#L99-L101

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

theorem PositivityTheory.Rg.Sw.LVs.incl_mul (s : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ) : (incl s)ᵀ * M * incl s = subOn s M := by sorry
