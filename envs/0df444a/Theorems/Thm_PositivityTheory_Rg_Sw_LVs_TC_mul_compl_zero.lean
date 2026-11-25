-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_mul_compl_zero
-- name    : PositivityTheory.Rg.Sw.LVs.TC.mul_compl_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:49:11.171012+00:00
-- url     : https://prove2.me/theorems/524a4d9c-2674-4c4c-a077-d41107bf070a
-- title:
--   TC: mul compl zero
-- statement:
--   The TC construction uses the mul compl zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TCMatB.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TCMatB.lean#L40-L42

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatA
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlkB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.TC.mul_compl_zero (j : ℕ) (Q S : Matrix (Fin n) (Fin n) ℂ) (hQ : ∀ a b, Q a b ≠ 0 → b ∈ blkA j)
    (hS : ∀ a b, S a b ≠ 0 → a ∈ blkB j) : Q * S = 0 := by sorry
