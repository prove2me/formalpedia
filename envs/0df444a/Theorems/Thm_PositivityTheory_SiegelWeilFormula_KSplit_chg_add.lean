-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_chg_add
-- name    : PositivityTheory.SiegelWeilFormula.KSplit.chg_add
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:03:30.176164+00:00
-- url     : https://prove2.me/theorems/4a5c3b99-fbe3-416b-9037-46a356a739bc
-- title:
--   KSplit: chg add
-- statement:
--   The KSplit construction uses the chg add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L164-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L164-L168

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

theorem PositivityTheory.SiegelWeilFormula.KSplit.chg_add (a : Fin m) (k : Fin m × Fin n × Bool) (e : ℕ) (s : Fin m × Fin n × Bool →₀ ℕ) :
    chg a (Finsupp.single k e + s) = (if k.1 = a then (if k.2.2 then -(e : ℤ) else e) else 0) + chg a s := by sorry
