-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_lin_lf
-- name    : PositivityTheory.SiegelWeilFormula.KSplit.lin_lf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:11.628171+00:00
-- url     : https://prove2.me/theorems/0294cd92-50e4-401e-ad9b-fc61066fda44
-- title:
--   KSplit: lin lf
-- statement:
--   The KSplit construction uses the lin lf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L25-L31

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

theorem PositivityTheory.SiegelWeilFormula.KSplit.lin_lf (φ : PX m n →ₗ[ℂ] PX m n) (b : Bool) (N M : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) (i : Fin n)
    (h : ∀ c, φ (X (c, i, b)) = lf b N c i) : φ (lf b M a i) = lf b (M * N) a i := by sorry
