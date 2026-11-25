-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_T_Delta_eq
-- name    : PositivityTheory.Rg.Sw.WR.T.Delta_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:02:11.596078+00:00
-- url     : https://prove2.me/theorems/2d7ae9c5-2cbd-402a-873d-a1865470d0d0
-- title:
--   T: Delta eq
-- statement:
--   The T construction uses the Delta eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DifferentiableOfTop.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DifferentiableOfTop.lean#L65-L68

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DifferentiableOfTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.T
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.T.Delta_eq (f : E n → ℂ) :
    Delta f = fun y => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * FD (Ls σ) f y := by sorry
