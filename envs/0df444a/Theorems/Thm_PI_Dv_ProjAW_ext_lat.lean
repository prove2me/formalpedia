-- Prove2me | Theorems.Thm_PI_Dv_ProjAW_ext_lat
-- name    : PI.Dv.ProjAW.ext_lat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:16.642972+00:00
-- url     : https://prove2.me/theorems/a3457e17-139a-422f-9134-2b64e521c223
-- title:
--   Proj AW: ext lat
-- statement:
--   The Proj AW construction uses the ext lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LengthIndex/MemDualLat.lean#L12-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LengthIndex/MemDualLat.lean#L12-L49

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

theorem PI.Dv.ProjAW.ext_lat {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (L : Submodule (𝓞 K) V) (hL : Submodule.span K (L : Set V) = ⊤) (g : L →ₗ[𝓞 K] K) :
    ∃ φ : V →ₗ[K] K, ∀ a : L, φ a = g a := by sorry
