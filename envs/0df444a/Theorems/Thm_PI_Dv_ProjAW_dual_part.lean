-- Prove2me | Theorems.Thm_PI_Dv_ProjAW_dual_part
-- name    : PI.Dv.ProjAW.dual_part
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:40.229834+00:00
-- url     : https://prove2.me/theorems/01fd4893-b23d-4053-8b7a-993c5a0e335c
-- title:
--   Proj AW: dual part
-- statement:
--   The Proj AW construction uses the dual part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LengthIndex/MemDualLat.lean#L57-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LengthIndex/MemDualLat.lean#L57-L129

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_LenAtEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_MemDualLat
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
variable {K : Type} [Field K] [NumberField K]
variable [StarRing K] (A : HLat K)

theorem PI.Dv.ProjAW.dual_part (hG : A.Good) {e : Module.End K A.V} (he : e * e = e) {n : ℕ} (hn0 : 0 < n)
    (hn : ∀ x ∈ A.L, ((n : ℕ) : 𝓞 K) • e x ∈ A.L) (ψ : Module.Dual K A.V) (hψ : ψ ∘ₗ e = ψ) :
    ψ ∈ Formalism.HN.dualLat (cutE A e A.L) ↔ ∃ φ ∈ A.dualL, ψ = φ ∘ₗ e := by sorry
