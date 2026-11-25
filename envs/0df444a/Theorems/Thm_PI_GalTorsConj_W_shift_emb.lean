-- Prove2me | Theorems.Thm_PI_GalTorsConj_W_shift_emb
-- name    : PI.GalTorsConj.W.shift_emb
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:31:50.331037+00:00
-- url     : https://prove2.me/theorems/94b49785-e07c-499a-8df9-ad85aa3ddf85
-- title:
--   W: shift emb
-- statement:
--   The W construction uses the shift emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/TorsValsFinite.lean#L28-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/TorsValsFinite.lean#L28-L48

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

theorem PI.GalTorsConj.W.shift_emb (M : IntermediateField ℚ ℂ) (x : ℂ) (hx : Transcendental M x) (k : ℕ) :
    ∃ σ : IntermediateField.adjoin M {x} →ₐ[M] ℂ,
      σ (IntermediateField.AdjoinSimple.gen M x) = x + k := by sorry
