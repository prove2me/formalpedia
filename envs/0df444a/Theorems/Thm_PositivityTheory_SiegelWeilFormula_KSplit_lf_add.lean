-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_lf_add
-- name    : PositivityTheory.SiegelWeilFormula.KSplit.lf_add
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:03:41.35311+00:00
-- url     : https://prove2.me/theorems/b3bf3edb-bf86-4dd5-a76b-9d4e69571bd8
-- title:
--   KSplit: lf add
-- statement:
--   The KSplit construction uses the lf add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L84-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L84-L86

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSplitting_ActUDiagMonomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KSplit
open PositivityTheory.Rg.Sw
variable {m n : ℕ}

theorem PositivityTheory.SiegelWeilFormula.KSplit.lf_add (b : Bool) (M N : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) (i : Fin n) :
    lf b (M + N) a i = lf b M a i + lf b N a i := by sorry
