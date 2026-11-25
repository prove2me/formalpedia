-- Prove2me | Theorems.Thm_PI_GalTorsConj_W_tors_vals_finite
-- name    : PI.GalTorsConj.W.tors_vals_finite
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:31:56.151845+00:00
-- url     : https://prove2.me/theorems/c9d1bd63-49b9-44a6-87d9-af72d112f0b8
-- title:
--   W: tors vals finite
-- statement:
--   The W construction uses the tors vals finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/TorsValsFinite.lean#L17-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/TorsValsFinite.lean#L17-L26

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_IncAdjInclusion
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpOnto
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddDbl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_TorsValsFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GalTorsConj PI.GalTorsConj.W
open Polynomial Formalism.L2.Th1.F

theorem PI.GalTorsConj.W.tors_vals_finite (L : PeriodPair) (n : ℕ) (hn : 0 < n) :
    {v : ℂ | ∃ s, (n : ℂ) * s ∈ L.lattice ∧ s ∉ L.lattice ∧ L.weierstrassP s = v}.Finite := by sorry
