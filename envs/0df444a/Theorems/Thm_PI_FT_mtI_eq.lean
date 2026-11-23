-- Prove2me | Theorems.Thm_PI_FT_mtI_eq
-- name    : PI.FT.mtI_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:00.64661+00:00
-- url     : https://prove2.me/theorems/ee109c94-da04-4a71-98a1-c3e0e4c02aad
-- title:
--   FT: mt I eq
-- statement:
--   The FT construction uses the mt I eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameTransport/InstIsModTopTens.lean#L99-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameTransport/InstIsModTopTens.lean#L99-L103

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_MemHFinInIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_InstIsModTopTens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FT
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}
local notation "ι" => inclR (F := F) (E := E) (AF F)

theorem PI.FT.mtI_eq {M' : ℕ} {J' : Matrix (Fin M') (Fin M') E}
    {K : Type} [Group K] (e : K ≃* HA (AF F) σ J') (g : K) :
    mtI (e g) = mt (e g⁻¹) := by sorry
