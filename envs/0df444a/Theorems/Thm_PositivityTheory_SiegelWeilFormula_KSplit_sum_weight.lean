-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_sum_weight
-- name    : PositivityTheory.SiegelWeilFormula.KSplit.sum_weight
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:03:54.462096+00:00
-- url     : https://prove2.me/theorems/5714c7d6-7251-4855-be07-86975ad35e75
-- title:
--   KSplit: sum weight
-- statement:
--   The KSplit construction uses the sum weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L211-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L211-L220

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

theorem PositivityTheory.SiegelWeilFormula.KSplit.sum_weight (d : Fin m → ℂ) (s : Fin m × Fin n × Bool →₀ ℕ) :
    (s.sum fun k e => (e : ℂ) * if k.2.2 then -d k.1 else d k.1) = ∑ a, d a * chg a s := by sorry
