-- Prove2me | Theorems.Thm_PI_WGB_natW_anti_A
-- name    : PI.WGB.natW_anti_A
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:49:17.486372+00:00
-- url     : https://prove2.me/theorems/a807c000-1625-4599-af6b-43d9ce5b6dfe
-- title:
--   WGB: nat W anti A
-- statement:
--   The WGB construction uses the nat W anti A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/ExtremalFactsProofA.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/ExtremalFactsProofA.lean#L21-L25

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFactsProofA
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

theorem PI.WGB.natW_anti_A {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by sorry
