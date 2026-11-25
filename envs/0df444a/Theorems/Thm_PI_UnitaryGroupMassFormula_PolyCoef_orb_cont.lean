-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_orb_cont
-- name    : PI.UnitaryGroupMassFormula.PolyCoef.orb_cont
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:21:12.500034+00:00
-- url     : https://prove2.me/theorems/b75bef86-576c-5d68-965a-ed259d95e852
-- title:
--   Poly Coef: orb cont
-- statement:
--   The Poly Coef construction uses the orb cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGroupIntegrability/IsPositiveDefiniteMatrixCoefficientOfMemAlgA.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGroupIntegrability/IsPositiveDefiniteMatrixCoefficientOfMemAlgA.lean#L32-L35

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeylForU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_InstCompactUG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_IsPositiveDefiniteMatrixCoefficientOfMemAlgA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PolyCoef
open MeasureTheory PI.UpqRep
open scoped InnerProductSpace
variable {N : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)} {S : Submodule ℂ H}

theorem PI.UnitaryGroupMassFormula.PolyCoef.orb_cont (hrep : IsURepOn (Kset (allPos N)) σ) (hst : IsKStableOn (allPos N) σ S) (u : S) :
    Continuous (orb hst u) := by sorry
