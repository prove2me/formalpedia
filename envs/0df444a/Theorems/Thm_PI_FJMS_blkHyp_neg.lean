-- Prove2me | Theorems.Thm_PI_FJMS_blkHyp_neg
-- name    : PI.FJMS.blkHyp_neg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:13.68117+00:00
-- url     : https://prove2.me/theorems/26ec703e-c4ba-4e0b-9c83-08ef8435d38b
-- title:
--   FJMS: blk Hyp neg
-- statement:
--   The FJMS construction uses the blk Hyp neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PosIffLtNP.lean#L210-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PosIffLtNP.lean#L210-L307

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Lemmata_B1959r_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PosIffLtNP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMS
open PI.FJM PI.FJMP
variable {p q r s : ℕ} {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {P : Pol p q r s}

theorem PI.FJMS.blkHyp_neg (hM : MinHyp p q r s μ μ' P) {m n : ℕ} (iX : Fin m → Ix p q) (jX : Fin n → Ix r s)
    (hi : Function.Injective iX) (hj : Function.Injective jX)
    (hmi : ∀ a b : Fin m, a < b → posC (iX b) (iX a)) (hmj : ∀ c d : Fin n, c < d → posC (jX d) (jX c))
    (hs1 : ∀ (a b : Fin m) (c : Ix r s), linePos ((iX b, c) : Ln p q r s) = linePos ((iX a, c) : Ln p q r s))
    (hs2 : ∀ (c d : Fin n) (a : Ix p q), linePos ((a, jX d) : Ln p q r s) = linePos ((a, jX c) : Ln p q r s))
    (hlp : ∀ i k, linePos ((iX i, jX k) : Ln p q r s) = false)
    (hcol : ∀ (i : Fin m) (c : Ix r s), linePos ((iX i, c) : Ln p q r s) = false → nu2 p q r s μ' c < 0 →
      c ∈ Set.range jX)
    (hrow : ∀ (k : Fin n) (a : Ix p q), linePos ((a, jX k) : Ln p q r s) = false → nu1 p q r s μ a < 0 →
      a ∈ Set.range iX)
    (hnu1 : ∀ i, nu1 p q r s μ (iX i) < 0) (hnu2 : ∀ k, nu2 p q r s μ' (jX k) < 0)
    (α : Fin m → ℕ) (β : Fin n → ℕ) (hα : ∀ i, α i = ⌊-nu1 p q r s μ (iX i)⌋₊)
    (hβ : ∀ k, β k = ⌊-nu2 p q r s μ' (jX k)⌋₊) :
    IsBlockHighestWeight (fun x : Fin m × Fin n => ((iX x.1, jX x.2) : Ln p q r s)) α β P := by sorry
