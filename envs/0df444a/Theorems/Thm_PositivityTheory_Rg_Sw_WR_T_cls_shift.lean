-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_T_cls_shift
-- name    : PositivityTheory.Rg.Sw.WR.T.cls_shift
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:02:59.207285+00:00
-- url     : https://prove2.me/theorems/d84455e0-6792-4a36-bbc3-744becc567b1
-- title:
--   T: cls shift
-- statement:
--   The T construction uses the cls shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsShift.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsShift.lean#L12-L15

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousHerm
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.T
open PositivityTheory.Rg.Sw

theorem PositivityTheory.Rg.Sw.WR.T.cls_shift {n : ℕ} (s z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (y : E n) :
    ((dP y : ℝ) : ℂ) ^ (-z) * cls s 0 p q R y = cls s z p q R y := by sorry
