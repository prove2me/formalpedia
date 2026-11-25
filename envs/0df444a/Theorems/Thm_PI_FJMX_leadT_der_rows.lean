-- Prove2me | Theorems.Thm_PI_FJMX_leadT_der_rows
-- name    : PI.FJMX.leadT_der_rows
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:37.289973+00:00
-- url     : https://prove2.me/theorems/3b7c2d3e-6ebb-4241-bae9-66be76351fde
-- title:
--   FJMX: lead T der rows
-- statement:
--   The FJMX construction uses the lead T der rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistHW.lean#L103-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistHW.lean#L103-L128

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

theorem PI.FJMX.leadT_der_rows (D : Derivation ℂ (Pol p q r s) (Pol p q r s)) (ρ : Fin m → Ix p q)
    (κ : Fin k → Ix r s) (t : ℕ)
    (h : ∀ i₀ : Fin m, i₀.val < t → (∀ j : Fin k, j.val < t → D (X (ρ i₀, κ j)) = 0) ∨
      ∃ i₁ : Fin m, i₁.val < t ∧ i₁ ≠ i₀ ∧ ∃ e : Pol p q r s,
        ∀ j : Fin k, j.val < t → D (X (ρ i₀, κ j)) = e * X (ρ i₁, κ j)) :
    D (leadT (varMat ρ κ) t) = 0 := by sorry
