-- Prove2me | Theorems.Thm_P2M_PI_WwMainW_Lfun_sum__0cd195b5fcc1
-- name    : P2M_PI_WwMainW_Lfun_sum__0cd195b5fcc1
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:02:18.456039+00:00
-- url     : https://prove2.me/theorems/a9db9d4c-3762-4f35-8ab2-25f4230a390a
-- title:
--   P2 M PI Ww Main W Lfun sum  0cd195b5fcc1: P2 M PI Ww Main W Lfun sum  0cd195b5fcc1
-- statement:
--   The P2 M PI Ww Main W Lfun sum  0cd195b5fcc1 construction uses the P2 M PI Ww Main W Lfun sum  0cd195b5fcc1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionMinors/LfunEqOfSubset.lean#L48-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionMinors/LfunEqOfSubset.lean#L48-L57

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_FintypeColChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_LfunEqOfSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open PI PI.WwMainW
open PI.WwMain PI.WwMain.KM

theorem P2M_PI_WwMainW_Lfun_sum__0cd195b5fcc1 {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) {ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial (Lt × Fin N0 × Fin N1) ℂ_[l]) :
    Lfun l N0 N1 Th (∑ i ∈ s, f i) = ∑ i ∈ s, Lfun l N0 N1 Th (f i) := by sorry

alias «PI».«WwMainW».«Lfun_sum'» := P2M_PI_WwMainW_Lfun_sum__0cd195b5fcc1
