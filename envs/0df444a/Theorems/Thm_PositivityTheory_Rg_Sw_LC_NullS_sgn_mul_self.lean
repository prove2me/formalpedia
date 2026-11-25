-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_sgn_mul_self
-- name    : PositivityTheory.Rg.Sw.LC.NullS.sgn_mul_self
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:48:44.721287+00:00
-- url     : https://prove2.me/theorems/35a63f57-7850-495a-8762-a4703a7cfded
-- title:
--   Null S: sgn mul self
-- statement:
--   The Null S construction uses the sgn mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PartialDerivQuadraticPairing.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PartialDerivQuadraticPairing.lean#L16-L17

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullOperatorEvaluation
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivQuadraticPairing
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.NullS
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.NullS.sgn_mul_self (ε : Fin m → Bool) (a : Fin m) : sgn ε a * sgn ε a = 1 := by sorry
