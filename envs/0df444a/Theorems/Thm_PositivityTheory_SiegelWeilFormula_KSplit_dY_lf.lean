-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_dY_lf
-- name    : PositivityTheory.SiegelWeilFormula.KSplit.dY_lf
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:20:24.412725+00:00
-- url     : https://prove2.me/theorems/40a70b64-6a72-4193-8da3-faeaeca7bb5b
-- title:
--   KSplit: d Y lf
-- statement:
--   The KSplit construction uses the d Y lf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L80-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L80-L82

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

theorem PositivityTheory.SiegelWeilFormula.KSplit.dY_lf (Y M : Matrix (Fin m) (Fin m) ℂ) (b : Bool) (a : Fin m) (i : Fin n) :
    dY Y (lf b M a i) = lf b (M * dm b Y) a i := by sorry
