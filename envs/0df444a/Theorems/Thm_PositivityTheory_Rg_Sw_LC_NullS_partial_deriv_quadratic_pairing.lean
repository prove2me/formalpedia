-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_partial_deriv_quadratic_pairing
-- name    : PositivityTheory.Rg.Sw.LC.NullS.partial_deriv_quadratic_pairing
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:44:30.29397+00:00
-- url     : https://prove2.me/theorems/a4a51ee7-f2ff-4536-b226-03b7a1daa987
-- title:
--   Null S: partial deriv quadratic pairing
-- statement:
--   The Null S construction uses the partial deriv quadratic pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PartialDerivQuadraticPairing.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PartialDerivQuadraticPairing.lean#L35-L39

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

theorem PositivityTheory.Rg.Sw.LC.NullS.partial_deriv_quadratic_pairing (ε : Fin m → Bool) (a : Fin m) (j k l : Fin n) :
    pderiv (a, j, true) (Qp ε k l : PX m n) = if k = j then C (sgn ε a) * X (a, l, false) else 0 := by sorry
