-- Prove2me | Theorems.Thm_PI_ParahoricIdxZ_W_theta_mul
-- name    : PI.ParahoricIdxZ.W.theta_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:35:58.301499+00:00
-- url     : https://prove2.me/theorems/be839f70-013d-51dd-ad4d-db7ee6176f78
-- title:
--   W: theta mul
-- statement:
--   The W construction uses the theta mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/ThetaInjective.lean#L46-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/ThetaInjective.lean#L46-L52

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

theorem PI.ParahoricIdxZ.W.theta_mul {a t : ℕ} {R : Type} [CommRing R] (A A' : Matrix (Fin a) (Fin a) R)
    (B B' : Matrix (Fin a) (Fin t) R) (C C' : Matrix (Fin t) (Fin a) R)
    (D D' : Matrix (Fin t) (Fin t) R) :
    theta A B C D * theta A' B' C' D' =
      theta (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by sorry
