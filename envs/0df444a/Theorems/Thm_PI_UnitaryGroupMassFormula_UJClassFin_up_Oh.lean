-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_up_Oh
-- name    : PI.UnitaryGroupMassFormula.UJClassFin.up_Oh
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:30:45.980271+00:00
-- url     : https://prove2.me/theorems/79201e52-5889-41ca-bb24-1593cedc1b74
-- title:
--   UJClass Fin: up Oh
-- statement:
--   The UJClass Fin construction uses the up Oh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/HermASingleLeft.lean#L63-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/HermASingleLeft.lean#L63-L73

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_RationalPointsDense
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_LatticeClassesFiniteRefinement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_PosDefOfDefiniteSignatureHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictInter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_HermASingleLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {M : ℕ}

theorem PI.UnitaryGroupMassFormula.UJClassFin.up_Oh (L : Set (Fin M → E)) {u : ℕ} (hu : ∀ x ∈ L, ∀ i, IsIntegral ℤ ((u : F) • x i))
    {w : Fin M → Af F ⊗[F] E} (hw : w ∈ latHat F E L) (i : Fin M) : u • w i ∈ Oh F E := by sorry
