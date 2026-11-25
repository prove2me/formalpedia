-- Prove2me | Theorems.Thm_PI_ParahoricIdxZ_W_theta_injective
-- name    : PI.ParahoricIdxZ.W.theta_injective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:36:10.067749+00:00
-- url     : https://prove2.me/theorems/dbf9f8cd-1126-442f-a165-b196faeeed42
-- title:
--   W: theta injective
-- statement:
--   The W construction uses the theta injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/ThetaInjective.lean#L38-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/ThetaInjective.lean#L38-L44

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_ThetaInjective
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
open PI PI.ParahoricIdxZ PI.ParahoricIdxZ.W
variable {F : Type} [Field F] (O : Subring F) (ϖ : F)

theorem PI.ParahoricIdxZ.W.theta_injective {a t : ℕ} {R : Type} {A A' : Matrix (Fin a) (Fin a) R}
    {B B' : Matrix (Fin a) (Fin t) R} {C C' : Matrix (Fin t) (Fin a) R}
    {D D' : Matrix (Fin t) (Fin t) R} (h : theta A B C D = theta A' B' C' D') :
    A = A' ∧ B = B' ∧ C = C' ∧ D = D' := by sorry
