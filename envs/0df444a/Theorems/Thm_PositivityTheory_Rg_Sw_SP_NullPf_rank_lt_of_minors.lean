-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_NullPf_rank_lt_of_minors
-- name    : PositivityTheory.Rg.Sw.SP.NullPf.rank_lt_of_minors
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:49:32.527+00:00
-- url     : https://prove2.me/theorems/083e3e85-9219-4c8f-a15a-246c52275f19
-- title:
--   Null Pf: rank lt of minors
-- statement:
--   The Null Pf construction uses the rank lt of minors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/DetEqZeroOfRankLt.lean#L61-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/DetEqZeroOfRankLt.lean#L61-L65

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_DetEqZeroOfRankLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Module
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.SP.NullPf
variable {K : Type*} [Field K]

theorem PositivityTheory.Rg.Sw.SP.NullPf.rank_lt_of_minors {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {k : ℕ}
    (h : ∀ I J : Fin k ↪ Fin n, (M.submatrix I J).det = 0) : M.rank < k := by sorry
