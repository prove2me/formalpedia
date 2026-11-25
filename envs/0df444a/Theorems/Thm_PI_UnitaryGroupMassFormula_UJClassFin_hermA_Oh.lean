-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_hermA_Oh
-- name    : PI.UnitaryGroupMassFormula.UJClassFin.hermA_Oh
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:42:40.111583+00:00
-- url     : https://prove2.me/theorems/9f6dd32c-9c77-43cc-8478-039add55e215
-- title:
--   UJClass Fin: herm A Oh
-- statement:
--   The UJClass Fin construction uses the herm A Oh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/HermASingleLeft.lean#L172-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/HermASingleLeft.lean#L172-L184

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
variable (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E)

theorem PI.UnitaryGroupMassFormula.UJClassFin.hermA_Oh {u dJ : ℕ} (hJ : ∀ i j, IsIntegral ℤ ((dJ : E) * J i j)) {X Y : Fin M → Af F ⊗[F] E}
    (hX : ∀ i, u • X i ∈ Oh F E) (hY : ∀ i, u • Y i ∈ Oh F E) :
    (u * u * dJ) • hermA σ J X Y ∈ Oh F E := by sorry
