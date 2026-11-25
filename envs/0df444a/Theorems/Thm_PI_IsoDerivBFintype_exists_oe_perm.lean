-- Prove2me | Theorems.Thm_PI_IsoDerivBFintype_exists_oe_perm
-- name    : PI.IsoDerivBFintype.exists_oe_perm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:08:09.817557+00:00
-- url     : https://prove2.me/theorems/0430d526-263b-41c5-937a-4a923dcae64c
-- title:
--   Iso Deriv BFintype: exists oe perm
-- statement:
--   The Iso Deriv BFintype construction uses the exists oe perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDerivative/ExistsOePerm.lean#L15-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDerivative/ExistsOePerm.lean#L15-L31

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ExistsOePerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.IsoDerivBFintype

theorem PI.IsoDerivBFintype.exists_oe_perm {h n : ℕ} (f : Fin h → Fin n) (hf : Function.Injective f) :
    ∃ (I : Fin h ↪o Fin n) (σ : Equiv.Perm (Fin h)), ∀ i, I (σ i) = f i := by sorry
