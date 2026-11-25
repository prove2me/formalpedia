-- Prove2me | Theorems.Thm_PI_FJMP_seg2
-- name    : PI.FJMP.seg2
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:31:36.426885+00:00
-- url     : https://prove2.me/theorems/855cc661-d28f-5880-8c6e-f1beca3ea53f
-- title:
--   FJMP: seg2
-- statement:
--   The FJMP construction uses the seg2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L447-L486
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L447-L486

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

theorem PI.FJMP.seg2 (hW1 : FormWt1) (hW2 : FormWt2) (hR2 : FormRaise2) {p q r s : ℕ} {μ : Ix p q → ℚ}
    {μ' : Ix r s → ℚ} {P : Pol p q r s} (hM : MinHyp p q r s μ μ' P) (c d : Ix r s) (hcd : posC c d)
    (hsame : ∀ a : Ix p q, linePos ((a, d) : Ln p q r s) = linePos ((a, c) : Ln p q r s)) :
    (0 < nu2 p q r s μ' d → 0 < nu2 p q r s μ' c) ∧ (nu2 p q r s μ' c < 0 → nu2 p q r s μ' d < 0) := by sorry
