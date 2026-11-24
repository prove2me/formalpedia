-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_actU_lf
-- name    : PositivityTheory.SiegelWeilFormula.KSplit.actU_lf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:36.319158+00:00
-- url     : https://prove2.me/theorems/7874ce1b-c097-4ee3-807c-d6f9adce76d2
-- title:
--   KSplit: act U lf
-- statement:
--   The KSplit construction uses the act U lf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L39-L41

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

theorem PositivityTheory.SiegelWeilFormula.KSplit.actU_lf (u M : Matrix (Fin m) (Fin m) ℂ) (b : Bool) (a : Fin m) (i : Fin n) :
    actU u (lf b M a i) = lf b (M * am b u) a i := by sorry
