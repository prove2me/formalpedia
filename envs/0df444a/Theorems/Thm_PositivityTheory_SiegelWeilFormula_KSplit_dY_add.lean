-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_dY_add
-- name    : PositivityTheory.SiegelWeilFormula.KSplit.dY_add
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:09:42.880467+00:00
-- url     : https://prove2.me/theorems/3c1d8ced-9658-5f8e-a972-9a68d8ef5df8
-- title:
--   KSplit: d Y add
-- statement:
--   The KSplit construction uses the d Y add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L92-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L92-L97

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

theorem PositivityTheory.SiegelWeilFormula.KSplit.dY_add (Y Y' : Matrix (Fin m) (Fin m) ℂ) : (dY (Y + Y') : Derivation ℂ (PX m n) (PX m n)) = dY Y + dY Y' := by sorry
