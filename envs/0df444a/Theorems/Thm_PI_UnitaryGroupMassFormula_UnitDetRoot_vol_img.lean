-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_vol_img
-- name    : PI.UnitaryGroupMassFormula.UnitDetRoot.vol_img
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:41:35.831435+00:00
-- url     : https://prove2.me/theorems/1892f11f-b5f5-46dc-a517-84f5016f85e2
-- title:
--   Unit Det Root: vol img
-- statement:
--   The Unit Det Root construction uses the vol img property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/GlobVol.lean#L34-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/GlobVol.lean#L34-L51

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

theorem PI.UnitaryGroupMassFormula.UnitDetRoot.vol_img (δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)) (Λ : AddSubgroup (m → ℂ)) :
    vol F (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λ)
      = Submodule.span (𝓞 F) {LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ))} * vol F Λ := by sorry
