-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_NullPf_det_eq_zero_of_rank_lt
-- name    : PositivityTheory.Rg.Sw.SP.NullPf.det_eq_zero_of_rank_lt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:49:23.772311+00:00
-- url     : https://prove2.me/theorems/bcd76cbf-76aa-42db-b143-3ee13ba90316
-- title:
--   Null Pf: det eq zero of rank lt
-- statement:
--   The Null Pf construction uses the det eq zero of rank lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/DetEqZeroOfRankLt.lean#L75-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/DetEqZeroOfRankLt.lean#L75-L79

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

theorem PositivityTheory.Rg.Sw.SP.NullPf.det_eq_zero_of_rank_lt {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (h : M.rank < n) : M.det = 0 := by sorry
