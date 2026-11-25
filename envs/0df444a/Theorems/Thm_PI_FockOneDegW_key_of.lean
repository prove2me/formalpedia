-- Prove2me | Theorems.Thm_PI_FockOneDegW_key_of
-- name    : PI.FockOneDegW.key_of
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:31:09.864081+00:00
-- url     : https://prove2.me/theorems/30f54eec-2e10-423b-a2b9-e4ee7f1c1958
-- title:
--   Fock One Deg W: key of
-- statement:
--   The Fock One Deg W construction uses the key of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/SameBlockOfPosC.lean#L65-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/SameBlockOfPosC.lean#L65-L148

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_RaisingLoweringSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_SameBlockOfPosC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial FockRaiseLowInner
open PI PI.FockOneDegW

theorem PI.FockOneDegW.key_of (hI : InnerFacts) (hKc : KHc) (hKh : KHarm) (hHc : HcHarm) (hS : HarmSub)
    (hA : KAdj) (hE : HwExist) (hT : HwHarmDeg)
    {p q r s : ℕ} (μ : Ix p q → ℚ) (W : Submodule ℂ (Pol p q r s)) [FiniteDimensional ℂ W]
    (hWK : KStable (fockAct1 p q r s) W)
    (hWhw : ∀ (ν : Ix p q → ℚ) (w : Pol p q r s), w ∈ W → IsHW (fockAct1 p q r s) ν w → ν = μ)
    (P : Pol p q r s) (hPW : P ∈ W) (hH : Harm2 P) (e : ℕ)
    (he : homogeneousComponent e P ≠ 0) :
    (e : ℚ) = degW (cPair r s) μ := by sorry
