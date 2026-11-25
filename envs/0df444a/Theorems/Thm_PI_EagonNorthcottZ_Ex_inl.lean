-- Prove2me | Theorems.Thm_PI_EagonNorthcottZ_Ex_inl
-- name    : PI.EagonNorthcottZ.Ex_inl
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:37.905119+00:00
-- url     : https://prove2.me/theorems/ef3f26c8-22ed-423c-aa51-7967c3f90a70
-- title:
--   Eagon Northcott Z: Ex inl
-- statement:
--   The Eagon Northcott Z construction uses the Ex inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottIntegral/LatticeInjective.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottIntegral/LatticeInjective.lean#L14-L19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_DivisionPartitionTotal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_LatticeInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EagonNorthcottZ
open MvPolynomial

theorem PI.EagonNorthcottZ.Ex_inl {D : ℕ} (s : S D) :
    Ex D (rename Sum.inl s) = map (C : ℤ →+* MvPolynomial (Fin D) ℤ) s := by sorry
