-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_hC_comm
-- name    : PositivityTheory.Rg.Sw.LC.hC_comm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:58:43.881792+00:00
-- url     : https://prove2.me/theorems/9de6a1f2-1a2f-586f-8773-8df3f354e140
-- title:
--   LC: h C comm
-- statement:
--   The LC construction uses the h C comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ContrEqOfSubset.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ContrEqOfSubset.lean#L17-L20

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_GaussianMomentRecurrence
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ContrEqOfSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.hC_comm (c : ℝ) (p q : ℕ) : hC c p q = hC c q p := by sorry
