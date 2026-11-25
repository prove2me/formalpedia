-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_dY_smul
-- name    : PositivityTheory.SiegelWeilFormula.KSplit.dY_smul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:07:07.617601+00:00
-- url     : https://prove2.me/theorems/9e06ec6b-69f3-5ef6-95db-800ed94049e7
-- title:
--   KSplit: d Y smul
-- statement:
--   The KSplit construction uses the d Y smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L99-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L99-L104

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

theorem PositivityTheory.SiegelWeilFormula.KSplit.dY_smul (z : ℂ) (Y : Matrix (Fin m) (Fin m) ℂ) : (dY (z • Y) : Derivation ℂ (PX m n) (PX m n)) = z • dY Y := by sorry
