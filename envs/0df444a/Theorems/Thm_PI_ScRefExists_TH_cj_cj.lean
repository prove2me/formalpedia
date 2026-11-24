-- Prove2me | Theorems.Thm_PI_ScRefExists_TH_cj_cj
-- name    : PI.ScRefExists.TH.cj_cj
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:14:24.343344+00:00
-- url     : https://prove2.me/theorems/098e80b1-59ea-420c-a167-bb3012ea7212
-- title:
--   TH: cj cj
-- statement:
--   The TH construction uses the cj cj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/ThetaA.lean#L64-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/ThetaA.lean#L64-L66

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

theorem PI.ScRefExists.TH.cj_cj (P : HeightOneSpectrum (𝓞 I.E)) : cj I (cj I P) = P := by sorry
