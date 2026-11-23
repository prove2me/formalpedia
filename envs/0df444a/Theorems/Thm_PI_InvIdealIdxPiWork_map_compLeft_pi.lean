-- Prove2me | Theorems.Thm_PI_InvIdealIdxPiWork_map_compLeft_pi
-- name    : PI.InvIdealIdxPiWork.map_compLeft_pi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:43.582902+00:00
-- url     : https://prove2.me/theorems/97753b4a-683b-4c48-a8d7-1c96666af27f
-- title:
--   Inv Ideal Idx Pi Work: map comp Left pi
-- statement:
--   The Inv Ideal Idx Pi Work construction uses the map comp Left pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvertibleIdealIndex/SubmodulePiToAddSubgroup.lean#L10-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvertibleIdealIndex/SubmodulePiToAddSubgroup.lean#L10-L21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_InvIdealIdxPi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvertibleIdealIndex_SubmodulePiToAddSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvIdealIdxPiWork
open NumberField nonZeroDivisors

theorem PI.InvIdealIdxPiWork.map_compLeft_pi {ι : Type} {G G' : Type*} [AddGroup G] [AddGroup G'] (φ : G →+ G')
    (A : ι → AddSubgroup G) :
    (AddSubgroup.pi Set.univ A).map (φ.compLeft ι) =
      AddSubgroup.pi Set.univ (fun i => (A i).map φ) := by sorry
