-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_formalGroup_param_sq_norm
-- name    : ReciprocityTheory.ChartRestriction.L1.formalGroup_param_sq_norm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:28:18.183291+00:00
-- url     : https://prove2.me/theorems/d1e49137-cbf3-4299-a708-ae2898993168
-- title:
--   L1: formal Group param sq norm
-- statement:
--   The L1 construction uses the formal Group param sq norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/TorChord.lean#L79-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/TorChord.lean#L79-L83

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

theorem ReciprocityTheory.ChartRestriction.L1.formalGroup_param_sq_norm (W : WeierstrassCurve C) (hW : IntegralModel W) (P : W.toAffine.Point) (hP : InFormalGroupPoints P)
    (h0 : P ≠ 0) : ‖uOf P‖ ^ 2 * ‖px W P‖ = 1 := by sorry
