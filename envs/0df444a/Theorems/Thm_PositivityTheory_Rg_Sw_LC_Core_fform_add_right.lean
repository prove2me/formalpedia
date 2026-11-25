-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_Core_fform_add_right
-- name    : PositivityTheory.Rg.Sw.LC.Core.fform_add_right
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:55:18.951415+00:00
-- url     : https://prove2.me/theorems/a0c530af-d446-4067-bb5c-2d464b68da25
-- title:
--   Core: fform add right
-- statement:
--   The Core construction uses the fform add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/FformSmulRight.lean#L54-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/FformSmulRight.lean#L54-L63

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_EquivLift
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FformSmulRight
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Core
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.Core.fform_add_right (c : ℝ) (p q₁ q₂ : PX m n) : fform c p (q₁ + q₂) = fform c p q₁ + fform c p q₂ := by sorry
