-- Prove2me | Theorems.Thm_PI_WGB_fockF_eq_sum
-- name    : PI.WGB.fockF_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:57:29.951949+00:00
-- url     : https://prove2.me/theorems/2f1dab71-ccb0-44b9-b167-4f57682eaa9e
-- title:
--   WGB: fock F eq sum
-- statement:
--   The WGB construction uses the fock F eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/FockFRowActRight.lean#L54-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/FockFRowActRight.lean#L54-L70

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

theorem PI.WGB.fockF_eq_sum {σ : Type} (p q : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ))
    (hs : ∀ m, p.coeff m ≠ 0 → q.coeff m ≠ 0 → m ∈ s) :
    fockF p q = ∑ m ∈ s, p.coeff m * star (q.coeff m) * fct m := by sorry
