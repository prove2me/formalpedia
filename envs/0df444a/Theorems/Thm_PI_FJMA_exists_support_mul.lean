-- Prove2me | Theorems.Thm_PI_FJMA_exists_support_mul
-- name    : PI.FJMA.exists_support_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:21.567797+00:00
-- url     : https://prove2.me/theorems/a4de5e79-c3ce-4467-aa91-f25b90a25ccc
-- title:
--   FJMA: exists support mul
-- statement:
--   The FJMA construction uses the exists support mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/VarsZeroOfSupported.lean#L25-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/VarsZeroOfSupported.lean#L25-L56

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeProdVarMatNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_VarsZeroOfSupported
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
open PI PI.FJMA
open PI.FJM
variable {σ : Type}

theorem PI.FJMA.exists_support_mul {S : Set σ} {F G : MvPolynomial σ ℂ} (hF : F ∈ supported ℂ S) (hF0 : F ≠ 0)
    (hG : FreeOf S G) {e' : σ →₀ ℕ} (he' : e' ∈ G.support) :
    ∃ e ∈ (F * G).support, ∀ v ∉ S, e v = e' v := by sorry
