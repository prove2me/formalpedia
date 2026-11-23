-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_cr_false
-- name    : PositivityTheory.Rg.Sw.LC.cr_false
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:40.442811+00:00
-- url     : https://prove2.me/theorems/dc0e7c71-315a-46cd-a108-b2ec1771fbcc
-- title:
--   LC: cr false
-- statement:
--   The LC construction uses the cr false property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/HopPderivComm.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/HopPderivComm.lean#L23-L25

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_HopPderivComm
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

theorem PositivityTheory.Rg.Sw.LC.cr_false (c : ℝ) (a : Fin m) (i : Fin n) (Q : PX m n) :
    cr c (a, i, false) Q = -pderiv (a, i, false) Q + (2 * c : ℂ) • (X (a, i, true) * Q) := by sorry
