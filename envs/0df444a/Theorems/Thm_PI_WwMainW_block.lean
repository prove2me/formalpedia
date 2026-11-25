-- Prove2me | Theorems.Thm_PI_WwMainW_block
-- name    : PI.WwMainW.block
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:46:00.666273+00:00
-- url     : https://prove2.me/theorems/1d76ea62-283e-5c8f-9a81-9253ee1ad24d
-- title:
--   Ww Main W: block
-- statement:
--   The Ww Main W construction uses the block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionMinors/DeXCBOf.lean#L13-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionMinors/DeXCBOf.lean#L13-L47

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_FintypeColChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_DeXCBOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset Matrix
noncomputable section
open PI PI.WwMainW
open PI.WwMain PI.WwMain.KM

theorem PI.WwMainW.block (hCB : CBSorted) {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (z : Lt × Fin N0 × Fin N1 → ℂ_[l]) (y' : Lt → Fin N1 → ℕ → ℂ_[l]) (s : Lt) (p : ℕ) :
    Matrix.det (Matrix.of fun i j : Fin p => ∑ a : Fin N0,
        C (∑ b : Fin N1, z (s, a, b) * y' s b (j : ℕ)) *
          (X (s, (i : ℕ), a) : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l])) =
      ∑ J : Fin p ↪o Fin N1, C (Matrix.det (Matrix.of fun i j : Fin p => y' s (J i) (j : ℕ))) *
        chi l N0 N1 z (minorXZ N0 N1 s p J) := by sorry
