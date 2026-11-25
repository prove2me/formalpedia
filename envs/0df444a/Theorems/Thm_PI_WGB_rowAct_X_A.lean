-- Prove2me | Theorems.Thm_PI_WGB_rowAct_X_A
-- name    : PI.WGB.rowAct_X_A
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:45:52.432499+00:00
-- url     : https://prove2.me/theorems/5c26f515-d115-4514-8c9b-8de264ecb28f
-- title:
--   WGB: row Act X A
-- statement:
--   The WGB construction uses the row Act X A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/ExtremalFactsProofA.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/ExtremalFactsProofA.lean#L33-L35

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

theorem PI.WGB.rowAct_X_A {r n : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (v : Fin r × Fin n) :
    Formalism.GradedWeylDivisibility.rowAct ℂ M (X v) = ∑ b : Fin r, C (M v.1 b) * X (b, v.2) := by sorry
