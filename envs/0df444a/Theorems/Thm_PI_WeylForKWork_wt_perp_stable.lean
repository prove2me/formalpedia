-- Prove2me | Theorems.Thm_PI_WeylForKWork_wt_perp_stable
-- name    : PI.WeylForKWork.wt_perp_stable
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:45:43.355372+00:00
-- url     : https://prove2.me/theorems/0264730e-92a9-47be-a14c-31f10f89c026
-- title:
--   Weyl For KWork: wt perp stable
-- statement:
--   The Weyl For KWork construction uses the wt perp stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Weights.lean#L64-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Weights.lean#L64-L81

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_TrivKtype
import Definitions.Def_Lemmata_GeneralBFactLeftVariant_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Weights
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WeylForKWork
open PI PI.UpqRep Matrix
open scoped InnerProductSpace

theorem PI.WeylForKWork.wt_perp_stable {N : ℕ} (ε : Fin N → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (hσ : IsURepOn (Kset ε) σ) (X' X : Submodule ℂ H)
    (hX' : IsKStableOn ε σ X') (hX : IsKStableOn ε σ X) : IsKStableOn ε σ (X'ᗮ ⊓ X) := by sorry
