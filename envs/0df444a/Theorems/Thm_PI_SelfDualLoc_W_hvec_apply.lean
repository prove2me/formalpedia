-- Prove2me | Theorems.Thm_PI_SelfDualLoc_W_hvec_apply
-- name    : PI.SelfDualLoc.W.hvec_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:06:41.587305+00:00
-- url     : https://prove2.me/theorems/cf943752-2c79-4fa4-8a70-9f4f3dacf26b
-- title:
--   W: hvec apply
-- statement:
--   The W construction uses the hvec apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/HvecApply.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/HvecApply.lean#L20-L22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_HformSumRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_HvecApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
noncomputable section
open PI PI.SelfDualLoc PI.SelfDualLoc.W
open PI.SelfDualLoc

theorem PI.SelfDualLoc.W.hvec_apply {E : Type} [Field E] {n m : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) (y : Fin n → E) (i : Fin m) :
    hvec σ J x y i = hform σ J (x i) y := by sorry
