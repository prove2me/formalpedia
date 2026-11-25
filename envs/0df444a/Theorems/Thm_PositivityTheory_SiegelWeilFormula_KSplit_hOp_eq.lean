-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_hOp_eq
-- name    : PositivityTheory.SiegelWeilFormula.KSplit.hOp_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:03:39.756414+00:00
-- url     : https://prove2.me/theorems/50d6156c-ba31-46d9-9a32-66d2ae4b594e
-- title:
--   KSplit: h Op eq
-- statement:
--   The KSplit construction uses the h Op eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L288-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L288-L316

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

theorem PositivityTheory.SiegelWeilFormula.KSplit.hOp_eq (c : ℝ) (a b : Fin m) (P : PX m n) : hOp (fun _ => true) c a b P = dY (single a b 1) P := by sorry
