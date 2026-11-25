-- Prove2me | Theorems.Thm_PI_WwMainW_applyQ_eq
-- name    : PI.WwMainW.applyQ_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:45:50.792471+00:00
-- url     : https://prove2.me/theorems/a81cf7f6-ea3c-5943-a230-2175d9f43f15
-- title:
--   Ww Main W: apply Q eq
-- statement:
--   The Ww Main W construction uses the apply Q eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionMinors/InfinitePadicComplex.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionMinors/InfinitePadicComplex.lean#L27-L33

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_FintypeColChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_InfinitePadicComplex
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

theorem PI.WwMainW.applyQ_eq {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (Q : MvPolynomial (Lt × Fin N0 × ℕ) ℂ_[l])
    (y' : Lt → Fin N1 → ℕ → ℂ_[l]) :
    applyQ l N0 N1 Th Q y' = Lfun l N0 N1 Th (aeval (fun v : Lt × Fin N0 × ℕ => ∑ b : Fin N1,
      C (y' v.1 b v.2.2) * X ((v.1, v.2.1, b) : Lt × Fin N0 × Fin N1)) Q) := by sorry
