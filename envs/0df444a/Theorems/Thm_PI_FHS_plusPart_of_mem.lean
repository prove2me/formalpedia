-- Prove2me | Theorems.Thm_PI_FHS_plusPart_of_mem
-- name    : PI.FHS.plusPart_of_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:05:13.640655+00:00
-- url     : https://prove2.me/theorems/2a4cea6a-7259-45ae-96b1-c77271e4e898
-- title:
--   FHS: plus Part of mem
-- statement:
--   The FHS construction uses the plus Part of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/MinusPartOfMem.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/MinusPartOfMem.lean#L15-L21

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_ConjTransposeOneKronecker
import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_MinusPartOfMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix FockH1Action
open PI PI.FHS
variable {σ : Type*}

theorem PI.FHS.plusPart_of_mem {A : Module.End ℂ (MvPolynomial σ ℂ)} {d : ℕ} {P : MvPolynomial σ ℂ}
    (hP : P ∈ homog σ d) : plusPart A P = homogeneousComponent (d + 2) (A P) := by sorry
