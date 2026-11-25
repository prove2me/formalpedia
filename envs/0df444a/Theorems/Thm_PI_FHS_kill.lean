-- Prove2me | Theorems.Thm_PI_FHS_kill
-- name    : PI.FHS.kill
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:04:06.607496+00:00
-- url     : https://prove2.me/theorems/57cd69c5-71d2-5ee5-81ba-79de27794159
-- title:
--   FHS: kill
-- statement:
--   The FHS construction uses the kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/MinusPartOfMem.lean#L35-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/MinusPartOfMem.lean#L35-L53

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
variable {p q r s : ℕ}

theorem PI.FHS.kill {a b : ℕ} (A : Mat a b →ₗ[ℂ] Module.End ℂ (Pol p q r s))
    (hA : ∀ Z : Mat a b, IsPC Z → ∀ P Q, fockInner (A Z P) Q = - fockInner P (A Zᴴ Q))
    {d : ℕ} {z : Pol p q r s} (hz : z ∈ homog (Ix p q × Ix r s) (d + 2))
    (horth : ∀ Z : Mat a b, IsPC Z → ∀ g ∈ homog (Ix p q × Ix r s) d,
      fockInner (plusPart (A Z) g) z = 0)
    (Z : Mat a b) (hZ : IsPC Z) : minusPart (A Z) z = 0 := by sorry
