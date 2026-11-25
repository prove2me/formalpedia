-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_Core_fform_smul_right
-- name    : PositivityTheory.Rg.Sw.LC.Core.fform_smul_right
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:54:57.613368+00:00
-- url     : https://prove2.me/theorems/9706b7f0-1e40-49e3-8b08-06486cc0f0af
-- title:
--   Core: fform smul right
-- statement:
--   The Core construction uses the fform smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/FformSmulRight.lean#L65-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/FformSmulRight.lean#L65-L71

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

theorem PositivityTheory.Rg.Sw.LC.Core.fform_smul_right (c : ℝ) (p q : PX m n) (r : ℂ) : fform c p (r • q) = r * fform c p q := by sorry
