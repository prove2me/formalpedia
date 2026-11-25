-- Prove2me | Theorems.Thm_PI_TrDualLocW_main
-- name    : PI.TrDualLocW.main
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:37:36.455615+00:00
-- url     : https://prove2.me/theorems/e7abc8fe-b409-441d-8b8b-e255ebd81b8e
-- title:
--   Tr Dual Loc W: main
-- statement:
--   The Tr Dual Loc W construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceDualLocal/Imports.lean#L12-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceDualLocal/Imports.lean#L12-L137

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceDualLocal_IsIntegralNatCast
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountNonIntegrality_TraceOfKer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountNonIntegrality_T2SpaceOfNonarchimedeanLocalField
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceDualLocal_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.TrDualLocW
open NumberField ValuativeRel PI.CntNotIntW
open scoped TensorProduct

theorem PI.TrDualLocW.main {K : Type} [Field K] [NumberField K] {ℓ : ℕ} [Fact ℓ.Prime] {Fp : Type} [Field Fp]
    [CharZero Fp] [ValuativeRel Fp] [TopologicalSpace Fp] [IsNonarchimedeanLocalField Fp] [Algebra ℚ_[ℓ] Fp]
    (hc : Continuous (algebraMap ℚ_[ℓ] Fp)) (hfin : FiniteDimensional ℚ_[ℓ] Fp) (ι : K →+* Fp)
    (hsurj : Function.Surjective (piMap K ℓ Fp ι)) (t : K)
    (ht : ∀ a : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (t * a) = n) (c : Fp) (hcO : c ∈ 𝒪[Fp]) :
    ‖Algebra.trace ℚ_[ℓ] Fp (c * ι t)‖ ≤ 1 := by sorry
