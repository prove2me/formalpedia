-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_star_dot_self
-- name    : PositivityTheory.Rg.Sw.WR.B.star_dot_self
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:00:50.354506+00:00
-- url     : https://prove2.me/theorems/15b49e80-c4cd-4588-b418-9d50ca3bb756
-- title:
--   B: star dot self
-- statement:
--   The B construction uses the star dot self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundA.lean#L97-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundA.lean#L97-L100

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
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
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.B.star_dot_self (v : Fin n → ℂ) : (star v ⬝ᵥ v) = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by sorry
