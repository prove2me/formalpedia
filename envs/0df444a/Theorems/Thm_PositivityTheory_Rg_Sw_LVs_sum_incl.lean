-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_sum_incl
-- name    : PositivityTheory.Rg.Sw.LVs.sum_incl
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:01:49.893248+00:00
-- url     : https://prove2.me/theorems/d4dff926-ffbb-544b-a3dd-ae940087c96c
-- title:
--   LVs: sum incl
-- statement:
--   The LVs construction uses the sum incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulInverseCayley.lean#L78-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulInverseCayley.lean#L78-L89

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

theorem PositivityTheory.Rg.Sw.LVs.sum_incl (s : Finset (Fin n)) (a : Fin n) (f : s → ℂ) :
    ∑ i : s, (if a = (i : Fin n) then (1 : ℂ) else 0) * f i = if h : a ∈ s then f ⟨a, h⟩ else 0 := by sorry
