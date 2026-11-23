-- Prove2me | Theorems.Thm_PI_VolStabW_FFHS_IsSq_lin_apply
-- name    : PI.VolStabW.FFHS.IsSq.lin_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:13:34.818289+00:00
-- url     : https://prove2.me/theorems/81894de6-a689-4032-8c4f-836d1fa12c54
-- title:
--   Is Sq: lin apply
-- statement:
--   The Is Sq construction uses the lin apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensFFHS.lean#L31-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensFFHS.lean#L31-L31

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFHS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.FFHS
open Module
variable {K : Type} [Field K] {σ : K →+* K}
variable {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K}

theorem PI.VolStabW.FFHS.IsSq.lin_apply (hs : IsSq σ h) (x y : V) : hs.lin x y = h x y := by sorry
