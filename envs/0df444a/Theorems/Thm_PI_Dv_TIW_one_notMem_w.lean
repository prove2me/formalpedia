-- Prove2me | Theorems.Thm_PI_Dv_TIW_one_notMem_w
-- name    : PI.Dv.TIW.one_notMem_w
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:19:09.955414+00:00
-- url     : https://prove2.me/theorems/21d20185-58e9-48a2-92e1-b944bff03c2f
-- title:
--   TIW: one not Mem w
-- statement:
--   The TIW construction uses the one not Mem w property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/IdxNonnegOfLe.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/IdxNonnegOfLe.lean#L21-L22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxNonnegOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem PI.Dv.TIW.one_notMem_w (w : HeightOneSpectrum (𝓞 K)) : (1 : 𝓞 K) ∉ w.asIdeal := by sorry
