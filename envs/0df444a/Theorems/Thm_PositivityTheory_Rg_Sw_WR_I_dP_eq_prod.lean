-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_I_dP_eq_prod
-- name    : PositivityTheory.Rg.Sw.WR.I.dP_eq_prod
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:02:17.348285+00:00
-- url     : https://prove2.me/theorems/b539d48f-19cd-4e0d-bfd5-c14ed435810f
-- title:
--   I: d P eq prod
-- statement:
--   The I construction uses the d P eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/Integr.lean#L42-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/Integr.lean#L42-L87

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Integr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.I
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.I.dP_eq_prod (y : E n) :
    dP y = ∏ i, (1 + (herm_isHermitian y).eigenvalues i ^ 2) ∧
      ∑ a, ∑ b, y a b ^ 2 = ∑ i, (herm_isHermitian y).eigenvalues i ^ 2 := by sorry
