-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_ub_eq
-- name    : PositivityTheory.Rg.Sw.LVs.ub_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:59:34.636786+00:00
-- url     : https://prove2.me/theorems/44feb2bb-b5dc-456c-b1a8-82c802b96184
-- title:
--   LVs: ub eq
-- statement:
--   The LVs construction uses the ub eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L288-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L288-L292

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.ub_eq (Z : M2 n) :
    Z.toBlocks₁₁ + Complex.I • Z.toBlocks₂₁ = (Lr n * Z : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ) * Rc n := by sorry
