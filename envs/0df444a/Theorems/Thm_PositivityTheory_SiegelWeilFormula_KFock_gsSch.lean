-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFock_gsSch
-- name    : PositivityTheory.SiegelWeilFormula.KFock.gsSch
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:57:57.702623+00:00
-- url     : https://prove2.me/theorems/0947ea71-5384-4286-bf1e-b4137ba3306a
-- title:
--   KFock: gs Sch
-- statement:
--   The KFock construction uses the gs Sch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/FockSpaces/EvXTemperate.lean#L60-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/FockSpaces/EvXTemperate.lean#L60-L72

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_FockSpaces_EvXTemperate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped SchwartzMap
open PositivityTheory.Rg.Sw
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFock

theorem PositivityTheory.SiegelWeilFormula.KFock.gsSch (m n : ℕ) {c : ℝ} (hc : 0 < c) : ∃ G : 𝓢(Fin m → Fin n → ℂ, ℂ), ∀ x, G x = gs c x := by sorry
