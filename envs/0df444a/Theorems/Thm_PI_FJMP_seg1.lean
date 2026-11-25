-- Prove2me | Theorems.Thm_PI_FJMP_seg1
-- name    : PI.FJMP.seg1
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:51.851655+00:00
-- url     : https://prove2.me/theorems/d81b3e3f-c283-49e9-bcec-1082cf1cac2e
-- title:
--   FJMP: seg1
-- statement:
--   The FJMP construction uses the seg1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L406-L445
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L406-L445

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
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
open PI PI.FJMP
open PI.FJM

theorem PI.FJMP.seg1 (hW1 : FormWt1) (hW2 : FormWt2) (hR1 : FormRaise1) {p q r s : ℕ} {μ : Ix p q → ℚ}
    {μ' : Ix r s → ℚ} {P : Pol p q r s} (hM : MinHyp p q r s μ μ' P) (a b : Ix p q) (hab : posC a b)
    (hsame : ∀ c : Ix r s, linePos ((b, c) : Ln p q r s) = linePos ((a, c) : Ln p q r s)) :
    (0 < nu1 p q r s μ b → 0 < nu1 p q r s μ a) ∧ (nu1 p q r s μ a < 0 → nu1 p q r s μ b < 0) := by sorry
