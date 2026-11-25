-- Prove2me | Theorems.Thm_PI_UConjT_inner_toEuclideanLin_unitary
-- name    : PI.UConjT.inner_toEuclideanLin_unitary
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:31:45.068868+00:00
-- url     : https://prove2.me/theorems/84f7ffe9-691b-47e0-8bba-f4b2abdac13e
-- title:
--   UConj T: inner to Euclidean Lin unitary
-- statement:
--   The UConj T construction uses the inner to Euclidean Lin unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryConjugation/Transfer.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryConjugation/Transfer.lean#L11-L17

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_TransferStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_Transfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UConjT
open Matrix

theorem PI.UConjT.inner_toEuclideanLin_unitary {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (hg : gᴴ * g = 1)
    (x y : EuclideanSpace ℂ (Fin m)) :
    inner ℂ (Matrix.toEuclideanLin g x) (Matrix.toEuclideanLin g y) = inner ℂ x y := by sorry
