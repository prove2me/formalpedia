-- Prove2me | Theorems.Thm_PI_OpWords_iter_mem
-- name    : PI.OpWords.iter_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:16:22.856815+00:00
-- url     : https://prove2.me/theorems/c4911023-12dd-5647-8d75-83eaf5ea2444
-- title:
--   Op Words: iter mem
-- statement:
--   The Op Words construction uses the iter mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/VanishMain.lean#L46-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/VanishMain.lean#L46-L52

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_VanishExp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_VanishMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.OpWords
variable {K : Type} [Field K] [CharZero K] {k : ℕ}

theorem PI.OpWords.iter_mem (W : Submodule K (Pol K k)) (hst : ∀ f ∈ W, ∀ a b, Rop K k a b f ∈ W)
    (a b : Fin k) {g : Pol K k} (hg : g ∈ W) (n : ℕ) : (Rop K k a b)^[n] g ∈ W := by sorry
