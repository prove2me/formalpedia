-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_formalGroup_add_estimate
-- name    : ReciprocityTheory.ChartRestriction.L1.formalGroup_add_estimate
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:45:20.417662+00:00
-- url     : https://prove2.me/theorems/120d3ba9-0f91-468e-a3c1-b2b5c49d93f5
-- title:
--   L1: formal Group add estimate
-- statement:
--   The L1 construction uses the formal Group add estimate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/TorChord.lean#L147-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/TorChord.lean#L147-L154

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorDefs
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorChord
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

theorem ReciprocityTheory.ChartRestriction.L1.formalGroup_add_estimate [CompleteSpace C] (W : WeierstrassCurve C) (hW : IntegralModel W)
    (P Q : W.toAffine.Point) (hP : InFormalGroupPoints P) (hQ : InFormalGroupPoints Q) :
    ‖uOf (P + Q) - uOf P - uOf Q‖ ≤ (max ‖uOf P‖ ‖uOf Q‖) ^ 2 := by sorry
