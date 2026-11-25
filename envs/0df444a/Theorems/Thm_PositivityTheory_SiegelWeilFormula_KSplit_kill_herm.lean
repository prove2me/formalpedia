-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_kill_herm
-- name    : PositivityTheory.SiegelWeilFormula.KSplit.kill_herm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:03:39.629262+00:00
-- url     : https://prove2.me/theorems/6e3d7242-71b1-4471-a789-703faadce7f4
-- title:
--   KSplit: kill herm
-- statement:
--   The KSplit construction uses the kill herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L247-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L247-L256

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

theorem PositivityTheory.SiegelWeilFormula.KSplit.kill_herm (Λ : PX m n →ₗ[ℂ] ℂ) (hΛ : ∀ u ∈ unitaryGroup (Fin m) ℂ, ∀ P, Λ (actU u P) = Λ P)
    (H : Matrix (Fin m) (Fin m) ℂ) (hH : H.IsHermitian) (P : PX m n) : Λ (dY H P) = 0 := by sorry
