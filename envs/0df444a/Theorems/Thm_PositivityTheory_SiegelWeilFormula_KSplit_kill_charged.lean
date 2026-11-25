-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_kill_charged
-- name    : PositivityTheory.SiegelWeilFormula.KSplit.kill_charged
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:03:53.466792+00:00
-- url     : https://prove2.me/theorems/dc86db9f-8b8e-4ee7-86ce-1e07740366ad
-- title:
--   KSplit: kill charged
-- statement:
--   The KSplit construction uses the kill charged property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L188-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean#L188-L209

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

theorem PositivityTheory.SiegelWeilFormula.KSplit.kill_charged (Λ : PX m n →ₗ[ℂ] ℂ) (hΛ : ∀ u ∈ unitaryGroup (Fin m) ℂ, ∀ P, Λ (actU u P) = Λ P)
    (s : Fin m × Fin n × Bool →₀ ℕ) (a : Fin m) (h : chg a s ≠ 0) : Λ (monomial s 1) = 0 := by sorry
