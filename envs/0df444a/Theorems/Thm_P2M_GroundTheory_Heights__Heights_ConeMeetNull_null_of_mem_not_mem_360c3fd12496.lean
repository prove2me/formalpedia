-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMeetNull_null_of_mem_not_mem_360c3fd12496
-- name    : P2M_GroundTheory_Heights__Heights_ConeMeetNull_null_of_mem_not_mem_360c3fd12496
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:16:40.150475+00:00
-- url     : https://prove2.me/theorems/32bd0e66-8c50-4974-8762-1e6734f1c399
-- title:
--   P2 M Ground Theory Heights  Heights Cone Meet Null null of mem not mem 360c3fd12496: P2 M Ground Theory Heights  Heights Cone Meet Null null of mem not mem 360c3fd12496
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Meet Null null of mem not mem 360c3fd12496 construction uses the P2 M Ground Theory Heights  Heights Cone Meet Null null of mem not mem 360c3fd12496 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMeetNull.lean#L13-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMeetNull.lean#L13-L51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMeetNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsZeroLocusDimH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PZeroLocusDimH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMeetNull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_ConeMeetNull_null_of_mem_not_mem_360c3fd12496 (hZ : ZeroLocusDimH.Statement) {n e : ℕ} (h : HermNorm n)
    (W W' : Ideal (MvPolynomial (Fin n) ℂ)) [W.IsPrime]
    (hW : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ ((e + 1 : ℕ) : WithBot ℕ∞))
    (g : MvPolynomial (Fin n) ℂ) (hgW' : g ∈ W') (hgW : g ∉ W) :
    Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W ∩ coneBall h W') = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeMeetNull».«null_of_mem_not_mem» := P2M_GroundTheory_Heights__Heights_ConeMeetNull_null_of_mem_not_mem_360c3fd12496
