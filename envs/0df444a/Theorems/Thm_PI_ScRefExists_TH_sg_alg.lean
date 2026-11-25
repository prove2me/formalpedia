-- Prove2me | Theorems.Thm_PI_ScRefExists_TH_sg_alg
-- name    : PI.ScRefExists.TH.sg_alg
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:23:20.869002+00:00
-- url     : https://prove2.me/theorems/168cb3cc-d8f7-4e4a-948a-92a40a99fb04
-- title:
--   TH: sg alg
-- statement:
--   The TH construction uses the sg alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/ThetaA.lean#L27-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/ThetaA.lean#L27-L35

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.TH
variable (I : Formalism.MainNotions.S.AutInst)

theorem PI.ScRefExists.TH.sg_alg (c : 𝓞 I.F) : sg I (algebraMap (𝓞 I.F) (𝓞 I.E) c) = algebraMap (𝓞 I.F) (𝓞 I.E) c := by sorry
