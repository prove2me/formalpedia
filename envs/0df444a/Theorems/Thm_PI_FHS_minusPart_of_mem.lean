-- Prove2me | Theorems.Thm_PI_FHS_minusPart_of_mem
-- name    : PI.FHS.minusPart_of_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:05:26.693528+00:00
-- url     : https://prove2.me/theorems/4a1fc054-dc78-4344-b3ce-b0ec30400835
-- title:
--   FHS: minus Part of mem
-- statement:
--   The FHS construction uses the minus Part of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/MinusPartOfMem.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/MinusPartOfMem.lean#L23-L29

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

theorem PI.FHS.minusPart_of_mem {A : Module.End ℂ (MvPolynomial σ ℂ)} {d : ℕ} {Q : MvPolynomial σ ℂ}
    (hQ : Q ∈ homog σ (d + 2)) : minusPart A Q = homogeneousComponent d (A Q) := by sorry
