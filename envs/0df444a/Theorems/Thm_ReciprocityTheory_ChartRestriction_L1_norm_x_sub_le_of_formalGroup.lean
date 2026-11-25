-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_x_sub_le_of_formalGroup
-- name    : ReciprocityTheory.ChartRestriction.L1.norm_x_sub_le_of_formalGroup
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:54:07.843805+00:00
-- url     : https://prove2.me/theorems/232322a6-7aa1-5d17-82d2-e26ddd601d38
-- title:
--   L1: norm x sub le of formal Group
-- statement:
--   The L1 construction uses the norm x sub le of formal Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/TorClose.lean#L47-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/TorClose.lean#L47-L117

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorChord
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorClose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)
variable {C : Type} [NormedField C] [IsUltrametricDist C]

theorem ReciprocityTheory.ChartRestriction.L1.norm_x_sub_le_of_formalGroup (W : WeierstrassCurve C) (h1 : W.a₁ = 0) (h2 : W.a₂ = 0) (h3 : W.a₃ = 0)
    (hW : IntegralModel W) (A B : W.toAffine.Point) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAy : ‖py W A‖ ≤ 1) (hBy : ‖py W B‖ ≤ 1) (hs : A + B ≠ 0) (hsx : ‖px W (A + B)‖ ≤ 1)
    (hd : A - B ≠ 0) (hdx : InFormalGroupPoints (A - B)) : ‖px W A - px W B‖ ≤ ‖uOf (A - B)‖ := by sorry
