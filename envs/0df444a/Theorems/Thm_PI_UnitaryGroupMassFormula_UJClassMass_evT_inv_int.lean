-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_evT_inv_int
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.evT_inv_int
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:20:47.826984+00:00
-- url     : https://prove2.me/theorems/c4c3a0f3-0c0d-59c0-9a91-1be04f16b496
-- title:
--   UJClass Mass: ev T inv int
-- statement:
--   The UJClass Mass construction uses the ev T inv int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/AlgebraMapIntIntAf.lean#L42-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/AlgebraMapIntIntAf.lean#L42-L45

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_OneSubEvTInvInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_AlgebraMapIntIntAf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain PI.UnitaryGroupMassFormula.UJClassFin
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F : Type} [Field F] [NumberField F]

theorem PI.UnitaryGroupMassFormula.UJClassMass.evT_inv_int (X : Set (HeightOneSpectrum (𝓞 F))) (t : 𝓞 F) (ht : ∀ u ∈ X, t ∉ u.asIdeal) :
    evT X * algebraMap F (Af F) ((algebraMap (𝓞 F) F t)⁻¹) ∈ intAf F := by sorry
