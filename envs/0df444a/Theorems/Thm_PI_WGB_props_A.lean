-- Prove2me | Theorems.Thm_PI_WGB_props_A
-- name    : PI.WGB.props_A
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:46:04.335921+00:00
-- url     : https://prove2.me/theorems/3b1e1851-18d2-4e2d-834f-501e579a7361
-- title:
--   WGB: props A
-- statement:
--   The WGB construction uses the props A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/ProdMkPtA.lean#L112-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/ProdMkPtA.lean#L112-L129

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_CoeffRowActDiagA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_StepACleared
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ProdMkPtA
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
variable {n : ℕ}

theorem PI.WGB.props_A (lam : DomWeight (n + 1)) (mu : DomWeight n) (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hf : f ∈ nablaSq ℂ (n + 1) lam) (hfix : IsFixedW rfl lam mu f) :
    IsWeightedHomogeneous (colW (n + 1) (n + 1)) f lam.natW ∧ RInvA (fun x => eval x f) ∧
      lhwline_CInv (fun x => eval x f) ∧
      ∀ m ∈ f.support, ∀ a : Fin n, ∑ s, m (Fin.castSucc a, s) = kapA lam mu a := by sorry
