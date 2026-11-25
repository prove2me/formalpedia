-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_prod_phase
-- name    : PositivityTheory.SiegelWeilFormula.KSplit.prod_phase
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:04:01.316261+00:00
-- url     : https://prove2.me/theorems/2a519eb4-0263-40a0-bb42-7717ca2b5fe6
-- title:
--   KSplit: prod phase
-- statement:
--   The KSplit construction uses the prod phase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L170-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L170-L181

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

theorem PositivityTheory.SiegelWeilFormula.KSplit.prod_phase (a : Fin m) (z : ℂ) (hz : star z * z = 1) (s : Fin m × Fin n × Bool →₀ ℕ) :
    (s.prod fun k e => (if k.2.2 then star (if k.1 = a then z else 1) else (if k.1 = a then z else 1)) ^ e) =
      z ^ chg a s := by sorry
