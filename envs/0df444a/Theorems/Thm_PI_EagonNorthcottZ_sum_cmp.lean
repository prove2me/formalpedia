-- Prove2me | Theorems.Thm_PI_EagonNorthcottZ_sum_cmp
-- name    : PI.EagonNorthcottZ.sum_cmp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:45:01.476388+00:00
-- url     : https://prove2.me/theorems/f44c2cc4-87d9-55a9-9a63-3f826a23a874
-- title:
--   Eagon Northcott Z: sum cmp
-- statement:
--   The Eagon Northcott Z construction uses the sum cmp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottIntegral/LatticeInjective.lean#L29-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottIntegral/LatticeInjective.lean#L29-L41

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

theorem PI.EagonNorthcottZ.sum_cmp {D : ℕ} (f : P D) (B : Finset (Fin D →₀ ℕ)) (hB : (Ex D f).support ⊆ B) :
    ∑ β ∈ B, inx (monomial β 1) * cmp β f = f := by sorry
