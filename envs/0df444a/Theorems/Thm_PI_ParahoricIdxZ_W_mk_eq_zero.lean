-- Prove2me | Theorems.Thm_PI_ParahoricIdxZ_W_mk_eq_zero
-- name    : PI.ParahoricIdxZ.W.mk_eq_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:36:16.255333+00:00
-- url     : https://prove2.me/theorems/ad4c957d-c5a7-4e34-a504-c3a09d0615f2
-- title:
--   W: mk eq zero
-- statement:
--   The W construction uses the mk eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/CardRangeRedJ.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/CardRangeRedJ.lean#L35-L38

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_ThetaInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_CardRangeRedJ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures.P.GLRed
open PI PI.ParahoricIdxZ PI.ParahoricIdxZ.W
variable {F : Type} [Field F] (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O)

theorem PI.ParahoricIdxZ.W.mk_eq_zero {u : F} (hu : u ∈ O) (o : F) (ho : o ∈ O) (h : u = ϖ * o) :
    Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) (⟨u, hu⟩ : O) = 0 := by sorry
