-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_SplitIso_sigT_tmul_one
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso.sigT_tmul_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:46:34.220931+00:00
-- url     : https://prove2.me/theorems/c18ec148-e1fa-5495-9861-4136c94af210
-- title:
--   Split Iso: sig T tmul one
-- statement:
--   The Split Iso construction uses the sig T tmul one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/SplitIso.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/SplitIso.lean#L17-L18

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

theorem PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso.sigT_tmul_one (σ : E →ₐ[F] E) (a : E) : sigT (K := K) σ ((1 : K) ⊗ₜ[F] a) = (1 : K) ⊗ₜ[F] σ a := by sorry
