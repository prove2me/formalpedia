-- Prove2me | Theorems.Thm_PI_DatumBlockEigen_Main_phiU_zero
-- name    : PI.DatumBlockEigen.Main.phiU_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:27:05.122344+00:00
-- url     : https://prove2.me/theorems/2da5f68e-1d12-4aab-8c01-3feb70e3301c
-- title:
--   Main: phi U zero
-- statement:
--   The Main construction uses the phi U zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BlockEigenvalues/PhiUZero.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BlockEigenvalues/PhiUZero.lean#L61-L64

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DatumBlockEigen
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LemmaU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_IsIntInvOfUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_PhiUZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.DatumBlockEigen PI.DatumBlockEigen.Main
open PI.DatumBlockEigen.Unit Formalism.DoubleCosetMeasures
variable {F : Type} [Field F] {a t : ℕ}
variable (O : Subring F) (ϖ : F) (J' : Subgroup (GL (Fin a) F))

theorem PI.DatumBlockEigen.Main.phiU_zero (ρ : J' →* ℂˣ) (x : Matrix (Fin a ⊕ Fin t) (Fin a) F)
    (h : ¬ Supp O ϖ J' x) : phiU O ϖ J' ρ x = 0 := by sorry
