-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_sq_norm_le
-- name    : PositivityTheory.Rg.Sw.LC.NullS.sq_norm_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:50:25.173654+00:00
-- url     : https://prove2.me/theorems/c58bf87c-5203-4a73-8893-5fa5f2df9311
-- title:
--   Null S: sq norm le
-- statement:
--   The Null S construction uses the sq norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PolyExpBound.lean#L50-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PolyExpBound.lean#L50-L51

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_HasFDerivAtEvX
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SquareNormBound
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PolyExpBound
import Theorems.Thm_UpperTheory_Reformulated_B_SquareNormBound_sq_norm_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.NullS
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.NullS.sq_norm_le (x : Fin m → Fin n → ℂ) : ‖x‖ ^ 2 ≤ ∑ a, ∑ i, ‖x a i‖ ^ 2 := by sorry
