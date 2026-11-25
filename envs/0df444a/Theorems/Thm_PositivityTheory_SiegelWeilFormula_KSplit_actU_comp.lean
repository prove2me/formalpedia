-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_actU_comp
-- name    : PositivityTheory.SiegelWeilFormula.KSplit.actU_comp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:50:37.850895+00:00
-- url     : https://prove2.me/theorems/819a925e-f8d3-4e78-86af-70bb14bec2d8
-- title:
--   KSplit: act U comp
-- statement:
--   The KSplit construction uses the act U comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L43-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L43-L48

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

theorem PositivityTheory.SiegelWeilFormula.KSplit.actU_comp (A B : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) : actU A (actU B P) = actU (B * A) P := by sorry
