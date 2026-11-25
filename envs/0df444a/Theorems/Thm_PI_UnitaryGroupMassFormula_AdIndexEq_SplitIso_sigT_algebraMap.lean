-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_SplitIso_sigT_algebraMap
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso.sigT_algebraMap
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:38:18.160467+00:00
-- url     : https://prove2.me/theorems/d72f58be-c17c-4c55-9ed8-41ced9cf7713
-- title:
--   Split Iso: sig T algebra Map
-- statement:
--   The Split Iso construction uses the sig T algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/SplitIso.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/SplitIso.lean#L13-L15

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso
open scoped TensorProduct
variable {F E K : Type} [Field F] [Field E] [Algebra F E] [Field K] [Algebra F K]

theorem PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso.sigT_algebraMap (σ : E →ₐ[F] E) (x : K) :
    sigT σ (algebraMap K (K ⊗[F] E) x) = algebraMap K (K ⊗[F] E) x := by sorry
