-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_vol_smul_le
-- name    : PI.UnitaryGroupMassFormula.UnitDetRoot.vol_smul_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:41:32.531912+00:00
-- url     : https://prove2.me/theorems/20e9ac0b-960f-4efc-9f3f-c8b6db37f2cf
-- title:
--   Unit Det Root: vol smul le
-- statement:
--   The Unit Det Root construction uses the vol smul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/GlobVol.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/GlobVol.lean#L14-L23

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_IdealPowPrincipal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobVol
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NumberField ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
variable (F : IntermediateField ℚ ℂ) {m : Type} [Fintype m] [DecidableEq m]

theorem PI.UnitaryGroupMassFormula.UnitDetRoot.vol_smul_le {Λ Λ' : AddSubgroup (m → ℂ)} (c : ℂ) (h : ∀ x ∈ Λ, c • x ∈ Λ') :
    Submodule.span (𝓞 F) {c ^ Fintype.card m} * vol F Λ ≤ vol F Λ' := by sorry
