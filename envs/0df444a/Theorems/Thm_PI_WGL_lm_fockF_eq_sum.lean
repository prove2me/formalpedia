-- Prove2me | Theorems.Thm_PI_WGL_lm_fockF_eq_sum
-- name    : PI.WGL.lm_fockF_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:50.621919+00:00
-- url     : https://prove2.me/theorems/db7462ee-9926-44ac-b79c-aaccd82bd00f
-- title:
--   WGL: lm fock F eq sum
-- statement:
--   The WGL construction uses the lm fock F eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftAsm.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftAsm.lean#L17-L24

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftAsm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem PI.WGL.lm_fockF_eq_sum {σ : Type*} (f g : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ)) (hs : f.support ⊆ s) :
    Formalism.REAL.fockF f g =
      ∑ m ∈ s, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by sorry
