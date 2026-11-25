-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_SP_NullPf_rank_add_le__3654c0f2223f
-- name    : P2M_PositivityTheory_Rg_Sw_SP_NullPf_rank_add_le__3654c0f2223f
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:11:14.039486+00:00
-- url     : https://prove2.me/theorems/2fd998d8-6cb7-5cb5-b7be-fecb0eb579c7
-- title:
--   P2 M Positivity Theory Rg Sw SP Null Pf rank add le  3654c0f2223f: P2 M Positivity Theory Rg Sw SP Null Pf rank add le  3654c0f2223f
-- statement:
--   The P2 M Positivity Theory Rg Sw SP Null Pf rank add le  3654c0f2223f construction uses the P2 M Positivity Theory Rg Sw SP Null Pf rank add le  3654c0f2223f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/DetEqZeroOfRankLt.lean#L67-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/DetEqZeroOfRankLt.lean#L67-L73

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

theorem P2M_PositivityTheory_Rg_Sw_SP_NullPf_rank_add_le__3654c0f2223f {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) : (A + B).rank ≤ A.rank + B.rank := by sorry

alias «PositivityTheory».«Rg».«Sw».«SP».«NullPf».«rank_add_le'» := P2M_PositivityTheory_Rg_Sw_SP_NullPf_rank_add_le__3654c0f2223f
