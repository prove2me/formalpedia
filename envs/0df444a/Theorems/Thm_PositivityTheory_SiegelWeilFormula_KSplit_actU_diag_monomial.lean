-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_actU_diag_monomial
-- name    : PositivityTheory.SiegelWeilFormula.KSplit.actU_diag_monomial
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:52:16.186414+00:00
-- url     : https://prove2.me/theorems/fc6cd06b-91dc-56ef-adfd-bf33be8166ce
-- title:
--   KSplit: act U diag monomial
-- statement:
--   The KSplit construction uses the act U diag monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L145-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L145-L159

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

theorem PositivityTheory.SiegelWeilFormula.KSplit.actU_diag_monomial (ζ : Fin m → ℂ) (s : Fin m × Fin n × Bool →₀ ℕ) :
    actU (diagonal ζ) (monomial s 1) =
      C (s.prod fun k e => (if k.2.2 then star (ζ k.1) else ζ k.1) ^ e) * monomial s (1 : ℂ) := by sorry
