-- Prove2me | Theorems.Thm_PI_FJMX_leadingMinor_rightRootDerivation_neg
-- name    : PI.FJMX.leadingMinor_rightRootDerivation_neg
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:30:19.336243+00:00
-- url     : https://prove2.me/theorems/5a5b8e49-37b9-457f-8d32-ad9c68c38f45
-- title:
--   FJMX: leading Minor right Root Derivation neg
-- statement:
--   The FJMX construction uses the leading Minor right Root Derivation neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistHW.lean#L216-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistHW.lean#L216-L231

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistHW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial FockH1Action PI.FJM
noncomputable section
open PI PI.FJMX
variable {p q r s : ℕ}
variable {m k : ℕ}

theorem PI.FJMX.leadingMinor_rightRootDerivation_neg (x y : Ix r s) (hxy : x ≠ y) (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s)
    (t : ℕ) (hneg : ∀ i, linePos (ρ i, x) = false)
    (hcl : ∀ j₀ : Fin k, j₀.val < t → κ j₀ = x → ∃ j₁ : Fin k, j₁.val < t ∧ κ j₁ = y) :
    der2 x y (leadT (varMat ρ κ) t) = 0 := by sorry
