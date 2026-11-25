-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GB_trace_gram
-- name    : PositivityTheory.Rg.Sw.WR.G.GB.trace_gram
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:01:51.052334+00:00
-- url     : https://prove2.me/theorems/af2e8d23-eaa2-43d5-9b9a-aa9d491ca7a2
-- title:
--   GB: trace gram
-- statement:
--   The GB construction uses the trace gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/HermTranspose.lean#L35-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/HermTranspose.lean#L35-L51

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBaseB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_HermTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
open PositivityTheory.Rg.Sw.WR.G.GB

theorem PositivityTheory.Rg.Sw.WR.G.GB.trace_gram (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    (b * gramX ε x).trace = ∑ a, ((sgnR ε a : ℝ) : ℂ) * ∑ i, ∑ j, star (x a i) * bᵀ i j * x a j := by sorry
