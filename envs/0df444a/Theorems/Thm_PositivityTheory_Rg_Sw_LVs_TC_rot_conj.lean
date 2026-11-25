-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_rot_conj
-- name    : PositivityTheory.Rg.Sw.LVs.TC.rot_conj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:49:32.787076+00:00
-- url     : https://prove2.me/theorems/f89326ff-3fc4-4c69-aff6-3d5f95064f62
-- title:
--   TC: rot conj
-- statement:
--   The TC construction uses the rot conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/StarExpNegI.lean#L48-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/StarExpNegI.lean#L48-L64

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_StarExpNegI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.TC.rot_conj (j : ℕ) (θ : ℝ) (r s : Fin n) :
    Complex.exp (2 * θ * Complex.I) • (rot j θ * nU (single r s 1) * (rot j θ)⁻¹ - 1) =
      Cm n * (zLow j r s + Complex.exp (2 * θ * Complex.I) • zMid j r s +
        Complex.exp (2 * θ * Complex.I) ^ 2 • zTop j r s) * CmI n := by sorry
