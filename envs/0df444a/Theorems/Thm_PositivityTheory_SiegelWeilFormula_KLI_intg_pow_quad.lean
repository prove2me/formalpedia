-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_intg_pow_quad
-- name    : PositivityTheory.SiegelWeilFormula.KLI.intg_pow_quad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:12.203774+00:00
-- url     : https://prove2.me/theorems/187e81a1-6200-47ea-8e45-a1dcb9398173
-- title:
--   KLI: intg pow quad
-- statement:
--   The KLI construction uses the intg pow quad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalOperatorBlocks/IntgPowQuad.lean#L9-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalOperatorBlocks/IntgPowQuad.lean#L9-L34

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_IntgPowQuad
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KLI

theorem PositivityTheory.SiegelWeilFormula.KLI.intg_pow_quad {b : ℂ} (hb : b.re < 0) (k : ℕ) (c : ℂ) :
    Integrable (fun x : ℝ => (x : ℂ) ^ k * cexp (b * (x : ℂ) ^ 2 + c * x)) := by sorry
