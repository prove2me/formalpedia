-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_evX_actU
-- name    : PositivityTheory.SiegelWeilFormula.KSplit.evX_actU
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:57:15.504054+00:00
-- url     : https://prove2.me/theorems/225c3993-922f-41dd-8954-6c99462a6cf2
-- title:
--   KSplit: ev X act U
-- statement:
--   The KSplit construction uses the ev X act U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L57-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L57-L69

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

theorem PositivityTheory.SiegelWeilFormula.KSplit.evX_actU (u : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) (v : Matrix (Fin m) (Fin n) ℂ) :
    evX (actU u P) v = evX P (u * v) := by sorry
