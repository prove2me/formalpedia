-- Prove2me | Theorems.Thm_PI_VolStabSW_exOmT_of
-- name    : PI.VolStabSW.exOmT_of
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:44:01.740931+00:00
-- url     : https://prove2.me/theorems/d5af9003-0a3a-41c2-a0a7-04c0ca2d744e
-- title:
--   Vol Stab SW: ex Om T of
-- statement:
--   The Vol Stab SW construction uses the ex Om T of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/RestrProd.lean#L104-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/RestrProd.lean#L104-L130

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_RestrProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem PI.VolStabSW.exOmT_of (h1 : LocEx) (h2 : SdUniq) (h3 : FibPin) (h4 : MultFib) (h5 : RestrProd) :
    ExOmT := by sorry
