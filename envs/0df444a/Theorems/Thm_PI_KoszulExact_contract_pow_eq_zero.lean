-- Prove2me | Theorems.Thm_PI_KoszulExact_contract_pow_eq_zero
-- name    : PI.KoszulExact.contract_pow_eq_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:34:04.343853+00:00
-- url     : https://prove2.me/theorems/3a4c770a-cb8e-421a-a480-317912b2ed3b
-- title:
--   Koszul Exact: contract pow eq zero
-- statement:
--   The Koszul Exact construction uses the contract pow eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/ContractPowSuccMem.lean#L14-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/ContractPowSuccMem.lean#L14-L32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_Ii
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_ContractPowSuccMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v
open PI PI.KoszulExact
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

theorem PI.KoszulExact.contract_pow_eq_zero (N : Submodule R M) (f : Module.Dual R M) (hf : ∀ m ∈ N, f m = 0) :
    ∀ (j : ℕ) (x : ExteriorAlgebra R M), x ∈ (N.map (ExteriorAlgebra.ι R)) ^ j →
      CliffordAlgebra.contractLeft f x = 0 := by sorry
