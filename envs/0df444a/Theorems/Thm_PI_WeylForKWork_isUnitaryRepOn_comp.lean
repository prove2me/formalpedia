-- Prove2me | Theorems.Thm_PI_WeylForKWork_isUnitaryRepOn_comp
-- name    : PI.WeylForKWork.isUnitaryRepOn_comp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:45:09.510801+00:00
-- url     : https://prove2.me/theorems/57dc72a8-ceaa-5f50-a9a5-e9d7c964166d
-- title:
--   Weyl For KWork: is Unitary Rep On comp
-- statement:
--   The Weyl For KWork construction uses the is Unitary Rep On comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Blocks.lean#L120-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Blocks.lean#L120-L131

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Blocks
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
variable {N : ℕ}

theorem PI.WeylForKWork.isUnitaryRepOn_comp {n : ℕ} (ε : Fin N → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (ι : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin N) (Fin N) ℂ)
    (h1 : ι 1 = 1) (hmul : ∀ a b, ι (a * b) = ι a * ι b) (hmem : ∀ h ∈ Kset (allPos n), ι h ∈ Kset ε)
    (hcont : Continuous ι) (hσ : IsURepOn (Kset ε) σ) : IsURepOn (Kset (allPos n)) (fun h => σ (ι h)) := by sorry
