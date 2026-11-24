-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_single_mem
-- name    : PI.UnitaryGroupMassFormula.UJClassFin.single_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:09:23.298828+00:00
-- url     : https://prove2.me/theorems/16b36a77-d7f6-4d79-b78d-94173985bd84
-- title:
--   UJClass Fin: single mem
-- statement:
--   The UJClass Fin construction uses the single mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/RationalPointsDense.lean#L53-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/RationalPointsDense.lean#L53-L77

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_RationalPointsDense
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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {M : ℕ}

theorem PI.UnitaryGroupMassFormula.UJClassFin.single_mem (L : Set (Fin M → E)) {k : ℕ}
    (hk : ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : F) • e) ∈ L)
    {p : Af F ⊗[F] E} (hp : p ∈ Oh F E) (l : Fin M) : Pi.single l (k • p) ∈ latHat F E L := by sorry
