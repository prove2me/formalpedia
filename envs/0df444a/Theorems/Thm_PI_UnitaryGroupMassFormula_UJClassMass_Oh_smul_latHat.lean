-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_Oh_smul_latHat
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.Oh_smul_latHat
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:43:12.261292+00:00
-- url     : https://prove2.me/theorems/7a7b5b41-b663-4da5-8fcd-77fdcc51f7e9
-- title:
--   UJClass Mass: Oh smul lat Hat
-- statement:
--   The UJClass Mass construction uses the Oh smul lat Hat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjA.lean#L123-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjA.lean#L123-L140

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Matrix
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {M : ℕ}

theorem PI.UnitaryGroupMassFormula.UJClassMass.Oh_smul_latHat (L : Set (Fin M → E)) (hL : ∀ e : E, IsIntegral ℤ e → ∀ x ∈ L, e • x ∈ L)
    {z : Af F ⊗[F] E} (hz : z ∈ PI.UnitaryGroupMassFormula.UJClassFin.Oh F E) {y : Fin M → Af F ⊗[F] E}
    (hy : y ∈ latHat F E L) : z • y ∈ latHat F E L := by sorry
