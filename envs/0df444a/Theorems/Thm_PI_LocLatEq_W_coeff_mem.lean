-- Prove2me | Theorems.Thm_PI_LocLatEq_W_coeff_mem
-- name    : PI.LocLatEq.W.coeff_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:15:23.849778+00:00
-- url     : https://prove2.me/theorems/cc95dae5-a934-4c05-923d-57befc90fe93
-- title:
--   W: coeff mem
-- statement:
--   The W construction uses the coeff mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeEquality/EpNontrivial.lean#L31-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeEquality/EpNontrivial.lean#L31-L95

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_EpNontrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc Polynomial
open PI PI.LocLatEq PI.LocLatEq.W
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

theorem PI.LocLatEq.W.coeff_mem (h2 : Module.finrank F E = 2) (A : LocAt F E sig p) (a : E)
    (ha : IsIntegral 𝒪[A.Fp] (A.ιE a)) (hnot : a ∉ (algebraMap F E).range) (i : ℕ) :
    A.ιF ((minpoly F a).coeff i) ∈ 𝒪[A.Fp] := by sorry
