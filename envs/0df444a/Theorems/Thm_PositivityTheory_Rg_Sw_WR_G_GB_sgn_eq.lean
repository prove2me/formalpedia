-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GB_sgn_eq
-- name    : PositivityTheory.Rg.Sw.WR.G.GB.sgn_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:07:21.158368+00:00
-- url     : https://prove2.me/theorems/246d4370-6863-5a8a-a48f-f31b05ad1810
-- title:
--   GB: sgn eq
-- statement:
--   The GB construction uses the sgn eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/HermTranspose.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/HermTranspose.lean#L19-L20

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

theorem PositivityTheory.Rg.Sw.WR.G.GB.sgn_eq (ε : Fin m → Bool) (a : Fin m) : sgn ε a = ((sgnR ε a : ℝ) : ℂ) := by sorry
