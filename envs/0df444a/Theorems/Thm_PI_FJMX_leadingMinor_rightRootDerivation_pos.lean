-- Prove2me | Theorems.Thm_PI_FJMX_leadingMinor_rightRootDerivation_pos
-- name    : PI.FJMX.leadingMinor_rightRootDerivation_pos
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:30:39.281175+00:00
-- url     : https://prove2.me/theorems/f7a977e5-7104-4c30-a5e1-06995505042f
-- title:
--   FJMX: leading Minor right Root Derivation pos
-- statement:
--   The FJMX construction uses the leading Minor right Root Derivation pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistHW.lean#L199-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistHW.lean#L199-L214

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

theorem PI.FJMX.leadingMinor_rightRootDerivation_pos (x y : Ix r s) (hxy : x ≠ y) (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s)
    (t : ℕ) (hpos : ∀ i, linePos (ρ i, x) = true)
    (hcl : ∀ j₀ : Fin k, j₀.val < t → κ j₀ = y → ∃ j₁ : Fin k, j₁.val < t ∧ κ j₁ = x) :
    der2 x y (leadT (varMat ρ κ) t) = 0 := by sorry
