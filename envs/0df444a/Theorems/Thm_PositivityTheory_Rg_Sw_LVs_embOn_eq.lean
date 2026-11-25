-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_embOn_eq
-- name    : PositivityTheory.Rg.Sw.LVs.embOn_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:02:19.244517+00:00
-- url     : https://prove2.me/theorems/3c56d6be-2b91-51ea-ab0e-53ae08a52679
-- title:
--   LVs: emb On eq
-- statement:
--   The LVs construction uses the emb On eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulInverseCayley.lean#L91-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulInverseCayley.lean#L91-L97

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

theorem PositivityTheory.Rg.Sw.LVs.embOn_eq (s : Finset (Fin n)) (T : Matrix s s ℂ) : embOn s T = incl s * T * (incl s)ᵀ := by sorry
