-- Prove2me | Theorems.Thm_PI_Dv_ProjAW_idx_le
-- name    : PI.Dv.ProjAW.idx_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:56:09.987745+00:00
-- url     : https://prove2.me/theorems/328254d4-5b22-50c1-9059-c1a4d10d4599
-- title:
--   Proj AW: idx le
-- statement:
--   The Proj AW construction uses the idx le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LengthIndex/IdxEqLen.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LengthIndex/IdxEqLen.lean#L14-L19

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

theorem PI.Dv.ProjAW.idx_le (hI : IdxCalc) (hG : A.Good) {f : Module.End K A.V} (hf : f * f = f) {n : ℕ}
    (hn0 : 0 < n) (hn : ∀ x ∈ A.L, ((n : ℕ) : 𝓞 K) • f x ∈ A.L) (w : HeightOneSpectrum (𝓞 K)) :
    idxAt w (imgE A f A.L) (cutE A f A.L) ≤ (dimE A f : ℤ) * vAdd w ((n : ℕ) : K) := by sorry
