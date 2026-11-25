-- Prove2me | Theorems.Thm_PI_SlopeSteps_expand
-- name    : PI.SlopeSteps.expand
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:39:28.082197+00:00
-- url     : https://prove2.me/theorems/17051d26-3d6f-431c-9950-231429f68953
-- title:
--   Slope Steps: expand
-- statement:
--   The Slope Steps construction uses the expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StandardSlopeBound/GramMatrixDuality.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StandardSlopeBound/GramMatrixDuality.lean#L44-L50

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_NablaBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_GramMatrixDuality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SlopeSteps
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.L2.DIV

theorem PI.SlopeSteps.expand {N r : ℕ} {M : Submodule ℤ (MvPolynomial (Fin N × Fin N) ℤ)} (e : Module.Basis (Fin r) ℤ M)
    (p : MvPolynomial (Fin N × Fin N) ℤ) (hp : p ∈ M) :
    intQ N N p = ∑ k, ((e.repr ⟨p, hp⟩ k : ℤ) : ℚ) • intQ N N (e k : MvPolynomial (Fin N × Fin N) ℤ) := by sorry
