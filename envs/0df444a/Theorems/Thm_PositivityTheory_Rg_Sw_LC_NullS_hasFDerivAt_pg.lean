-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_hasFDerivAt_pg
-- name    : PositivityTheory.Rg.Sw.LC.NullS.hasFDerivAt_pg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:43:59.005815+00:00
-- url     : https://prove2.me/theorems/13b55822-e0ac-45d1-b7e6-1e2d3a95bdb1
-- title:
--   Null S: has FDeriv At pg
-- statement:
--   The Null S construction uses the has FDeriv At pg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/NullOperatorEvaluation.lean#L51-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/NullOperatorEvaluation.lean#L51-L59

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PolyExpBound
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullOperatorEvaluation
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

theorem PositivityTheory.Rg.Sw.LC.NullS.hasFDerivAt_pg (c : ℝ) (P : PX m n) (x : Fin m → Fin n → ℂ) :
    HasFDerivAt (fun y => evX P y * gs c y) (evX P x • (gs c x • dP (Sg c) x) + gs c x • dP P x) x := by sorry
