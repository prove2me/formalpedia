-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_gramX_star
-- name    : PositivityTheory.Rg.Sw.WR.D.gramX_star
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:01:48.309273+00:00
-- url     : https://prove2.me/theorems/3ee3a7a6-2e25-4281-9e5f-ba95c8b2f8e9
-- title:
--   D: gram X star
-- statement:
--   The D construction uses the gram X star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ContinuousEvX.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ContinuousEvX.lean#L13-L16

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvX
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.D.gramX_star (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (i j : Fin n) :
    star (gramX ε x i j) = gramX ε x j i := by sorry
