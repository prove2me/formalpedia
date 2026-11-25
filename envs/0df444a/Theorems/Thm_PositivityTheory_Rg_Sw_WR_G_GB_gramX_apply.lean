-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GB_gramX_apply
-- name    : PositivityTheory.Rg.Sw.WR.G.GB.gramX_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:01:39.160231+00:00
-- url     : https://prove2.me/theorems/b08f0f41-c254-45a2-8dd9-1488642ff4d6
-- title:
--   GB: gram X apply
-- statement:
--   The GB construction uses the gram X apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/HermTranspose.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/HermTranspose.lean#L26-L33

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

theorem PositivityTheory.Rg.Sw.WR.G.GB.gramX_apply (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (i j : Fin n) :
    gramX ε x i j = ∑ a, ((sgnR ε a : ℝ) : ℂ) * (star (x a i) * x a j) := by sorry
