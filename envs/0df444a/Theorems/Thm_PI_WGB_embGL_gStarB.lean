-- Prove2me | Theorems.Thm_PI_WGB_embGL_gStarB
-- name    : PI.WGB.embGL_gStarB
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:46:48.40172+00:00
-- url     : https://prove2.me/theorems/8aba520d-5f8d-4de5-baba-7bbd4c61ef52
-- title:
--   WGB: emb GL g Star B
-- statement:
--   The WGB construction uses the emb GL g Star B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/FockFEqSumOfSubsetB.lean#L129-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/FockFEqSumOfSubsetB.lean#L129-L133

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ClosedEqNabla
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFEqSumOfSubsetB
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

theorem PI.WGB.embGL_gStarB {n N : ℕ} (h : n + 1 = N) (g : GL (Fin n) ℂ) :
    embGL ℂ n N h (gStarB g) = gStarB (embGL ℂ n N h g) := by sorry
