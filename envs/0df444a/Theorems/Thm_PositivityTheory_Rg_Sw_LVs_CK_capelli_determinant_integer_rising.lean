-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_capelli_determinant_integer_rising
-- name    : PositivityTheory.Rg.Sw.LVs.CK.capelli_determinant_integer_rising
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:50:09.606801+00:00
-- url     : https://prove2.me/theorems/d4959646-bebc-44b8-a899-276385175858
-- title:
--   CK: capelli determinant integer rising
-- statement:
--   The CK construction uses the capelli determinant integer rising property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/CayleyK.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/CayleyK.lean#L44-L50

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedDerivativeColumnCaseInt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CK
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem PositivityTheory.Rg.Sw.LVs.CK.capelli_determinant_integer_rising (t : ℤ) : ∀ N : ℕ, detD (H N t) = ∏ i ∈ Finset.range N, ((t : ℂ) + i)
  := by sorry
