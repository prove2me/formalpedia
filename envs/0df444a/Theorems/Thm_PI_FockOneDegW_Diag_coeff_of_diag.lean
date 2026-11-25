-- Prove2me | Theorems.Thm_PI_FockOneDegW_Diag_coeff_of_diag
-- name    : PI.FockOneDegW.Diag.coeff_of_diag
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:30:54.760516+00:00
-- url     : https://prove2.me/theorems/42f49d69-7ee2-4001-a441-76b9c6328d24
-- title:
--   Diag: coeff of diag
-- statement:
--   The Diag construction uses the coeff of diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/OmEDiagMonomial.lean#L96-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/OmEDiagMonomial.lean#L96-L113

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action
open PI PI.FockOneDegW PI.FockOneDegW.Diag

theorem PI.FockOneDegW.Diag.coeff_of_diag {σ : Type*} (T : Module.End ℂ (MvPolynomial σ ℂ)) (f : (σ →₀ ℕ) → ℂ)
    (hT : ∀ β, T (MvPolynomial.monomial β 1) = f β • MvPolynomial.monomial β 1)
    (P : MvPolynomial σ ℂ) (α : σ →₀ ℕ) :
    MvPolynomial.coeff α (T P) = f α * MvPolynomial.coeff α P := by sorry
