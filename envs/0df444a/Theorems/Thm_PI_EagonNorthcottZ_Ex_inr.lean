-- Prove2me | Theorems.Thm_PI_EagonNorthcottZ_Ex_inr
-- name    : PI.EagonNorthcottZ.Ex_inr
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:35.112215+00:00
-- url     : https://prove2.me/theorems/4fd47e78-0efa-53b1-bf6f-7a880e1127ba
-- title:
--   Eagon Northcott Z: Ex inr
-- statement:
--   The Eagon Northcott Z construction uses the Ex inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottIntegral/LatticeInjective.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottIntegral/LatticeInjective.lean#L21-L25

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

theorem PI.EagonNorthcottZ.Ex_inr {D : ℕ} (g : S D) : Ex D (rename Sum.inr g) = C g := by sorry
