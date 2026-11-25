-- Prove2me | Theorems.Thm_PI_WGB_natW_anti_D
-- name    : PI.WGB.natW_anti_D
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:57:29.639802+00:00
-- url     : https://prove2.me/theorems/24cd01b3-fd5a-5be2-ab86-d268e54e38f5
-- title:
--   WGB: nat W anti D
-- statement:
--   The WGB construction uses the nat W anti D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/ConstructionD.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/ConstructionD.lean#L10-L12

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ConstructionD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions MvPolynomial

theorem PI.WGB.natW_anti_D {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by sorry
