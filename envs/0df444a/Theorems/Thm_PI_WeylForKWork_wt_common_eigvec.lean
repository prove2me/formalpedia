-- Prove2me | Theorems.Thm_PI_WeylForKWork_wt_common_eigvec
-- name    : PI.WeylForKWork.wt_common_eigvec
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:47:30.969059+00:00
-- url     : https://prove2.me/theorems/ede0f80f-35c2-542c-86e5-ad736fbd1e32
-- title:
--   Weyl For KWork: wt common eigvec
-- statement:
--   The Weyl For KWork construction uses the wt common eigvec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Weights.lean#L20-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Weights.lean#L20-L58

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

theorem PI.WeylForKWork.wt_common_eigvec {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ι : Type}
    (A : ι → (H →L[ℂ] H)) (W : Submodule ℂ H) [FiniteDimensional ℂ W] (hW : W ≠ ⊥)
    (hst : ∀ i, ∀ v ∈ W, A i v ∈ W) (hcomm : ∀ i j, ∀ v, A i (A j v) = A j (A i v)) :
    ∃ w ∈ W, w ≠ 0 ∧ ∀ i, ∃ c : ℂ, A i w = c • w := by sorry
