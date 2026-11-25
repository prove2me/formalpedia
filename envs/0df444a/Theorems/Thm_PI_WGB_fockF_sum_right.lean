-- Prove2me | Theorems.Thm_PI_WGB_fockF_sum_right
-- name    : PI.WGB.fockF_sum_right
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:57:05.110403+00:00
-- url     : https://prove2.me/theorems/8ba0448e-f8fc-56ea-9c4f-6d900699f420
-- title:
--   WGB: fock F sum right
-- statement:
--   The WGB construction uses the fock F sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/FockFRowActRight.lean#L128-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/FockFRowActRight.lean#L128-L134

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFRowActRight
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
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.REAL (fockF)

theorem PI.WGB.fockF_sum_right {σ ι : Type} (s : Finset ι) (x : ι → MvPolynomial σ ℂ) (p : MvPolynomial σ ℂ) :
    fockF p (∑ i ∈ s, x i) = ∑ i ∈ s, fockF p (x i) := by sorry
