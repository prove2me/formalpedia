-- Prove2me | Theorems.Thm_PI_ScRefExists_TH_comap_cj
-- name    : PI.ScRefExists.TH.comap_cj
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:23:11.380114+00:00
-- url     : https://prove2.me/theorems/a3c13bdc-1618-40d2-a5cc-317ae6e7d9a3
-- title:
--   TH: comap cj
-- statement:
--   The TH construction uses the comap cj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/ThetaA.lean#L68-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/ThetaA.lean#L68-L71

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

theorem PI.ScRefExists.TH.comap_cj (P : HeightOneSpectrum (𝓞 I.E)) :
    (cj I P).asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = P.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) := by sorry
