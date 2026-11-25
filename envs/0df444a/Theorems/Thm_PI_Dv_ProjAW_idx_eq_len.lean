-- Prove2me | Theorems.Thm_PI_Dv_ProjAW_idx_eq_len
-- name    : PI.Dv.ProjAW.idx_eq_len
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:16.7737+00:00
-- url     : https://prove2.me/theorems/2cf08346-9e66-4df3-a7ad-d6da4de1e698
-- title:
--   Proj AW: idx eq len
-- statement:
--   The Proj AW construction uses the idx eq len property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LengthIndex/IdxEqLen.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LengthIndex/IdxEqLen.lean#L21-L25

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_MemDualLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_IdxEqLen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjAW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K] (A : HLat K)

theorem PI.Dv.ProjAW.idx_eq_len (w : HeightOneSpectrum (𝓞 K)) {f : Module.End K A.V} (hf : f * f = f) :
    idxAt w (imgE A f A.L) (cutE A f A.L) = ((lenAt w (imgE A f A.L) (cutE A f A.L)).toNat : ℤ) := by sorry
