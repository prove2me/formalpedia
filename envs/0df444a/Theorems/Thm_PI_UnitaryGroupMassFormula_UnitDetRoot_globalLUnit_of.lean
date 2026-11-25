-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_globalLUnit_of
-- name    : PI.UnitaryGroupMassFormula.UnitDetRoot.globalLUnit_of
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:34:51.865939+00:00
-- url     : https://prove2.me/theorems/03edc979-f269-5c76-a6b0-c59ae60981e3
-- title:
--   Unit Det Root: global LUnit of
-- statement:
--   The Unit Det Root construction uses the global LUnit of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/GlobTop.lean#L48-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/GlobTop.lean#L48-L125

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_IdealPowPrincipal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NumberField
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI Submodule NumberField

theorem PI.UnitaryGroupMassFormula.UnitDetRoot.globalLUnit_of
    (hV1 : ∀ (F : IntermediateField ℚ ℂ) (m : Type) [Fintype m] [DecidableEq m] (Λ Λ' : AddSubgroup (m → ℂ))
      (c : ℂ), (∀ x ∈ Λ, c • x ∈ Λ') → span (𝓞 F) {c ^ Fintype.card m} * vol F Λ ≤ vol F Λ')
    (hV2 : ∀ (F : IntermediateField ℚ ℂ) (m : Type) [Fintype m] [DecidableEq m]
      (δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)) (Λ : AddSubgroup (m → ℂ)),
      vol F (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λ) =
        span (𝓞 F) {LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ))} * vol F Λ)
    (hV3 : ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
      (m : Type) [Fintype m] [DecidableEq m], UnitDetRootDefs.CmOK a b c d →
      vol (KF b d) (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) ≤ span (𝓞 (KF b d)) {lam ^ Fintype.card m})
    (hV4 : ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
      (m : Type) [Fintype m] [DecidableEq m], UnitDetRootDefs.CmOK a b c d →
      vol (KF b d) (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) ≠ ⊥) :
    GlobalLUnit := by sorry
