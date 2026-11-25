-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_mstar_mul
-- name    : PositivityTheory.SiegelWeilFormula.KSplit.mstar_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:03:49.202591+00:00
-- url     : https://prove2.me/theorems/0048c6f0-0fa8-4d69-98ab-3ededb43182a
-- title:
--   KSplit: mstar mul
-- statement:
--   The KSplit construction uses the mstar mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L33-L34

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

theorem PositivityTheory.SiegelWeilFormula.KSplit.mstar_mul (A B : Matrix (Fin m) (Fin m) ℂ) : (A * B).map star = A.map star * B.map star := by sorry
