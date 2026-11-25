-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_NullPf_exists_minor_ne_zero
-- name    : PositivityTheory.Rg.Sw.SP.NullPf.exists_minor_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:13.9049+00:00
-- url     : https://prove2.me/theorems/5419dedd-a9bd-4e97-aae1-47a47b9cfa48
-- title:
--   Null Pf: exists minor ne zero
-- statement:
--   The Null Pf construction uses the exists minor ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/DetEqZeroOfRankLt.lean#L39-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/DetEqZeroOfRankLt.lean#L39-L59

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

theorem PositivityTheory.Rg.Sw.SP.NullPf.exists_minor_ne_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {k : ℕ} (hk : k ≤ M.rank) :
    ∃ I J : Fin k ↪ Fin n, (M.submatrix I J).det ≠ 0 := by sorry
