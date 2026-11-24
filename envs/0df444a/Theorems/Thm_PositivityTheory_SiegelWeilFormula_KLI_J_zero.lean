-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_J_zero
-- name    : PositivityTheory.SiegelWeilFormula.KLI.J_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:23.912204+00:00
-- url     : https://prove2.me/theorems/f59b4968-d71e-4b3b-9890-6e344e3900cc
-- title:
--   KLI: J zero
-- statement:
--   The KLI construction uses the J zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalOperatorBlocks/IntgPowQuad.lean#L123-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalOperatorBlocks/IntgPowQuad.lean#L123-L127

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

theorem PositivityTheory.SiegelWeilFormula.KLI.J_zero {b : ℂ} (hb : b.re < 0) (c : ℂ) :
    J b 0 c = (Real.pi / -b) ^ (1 / 2 : ℂ) * cexp (-(c ^ 2 / (4 * b))) := by sorry
