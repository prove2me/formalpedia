-- Prove2me | Theorems.Thm_PI_ScRefExists_GWG_crt_ge
-- name    : PI.ScRefExists.GWG.crt_ge
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:22:14.360854+00:00
-- url     : https://prove2.me/theorems/aca956fd-9f7d-4bc2-97d5-eeafc27bde43
-- title:
--   GWG: crt ge
-- statement:
--   The GWG construction uses the crt ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/GWGlue.lean#L81-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/GWGlue.lean#L81-L95

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GlobWIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GWGlue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.GWG
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)

theorem PI.ScRefExists.GWG.crt_ge {g₁ g₂ : ℕ} {A B q₁ q₂ : ℤ} (hq₁ : q₁ = g₂ * B) (hq₂ : q₂ = g₁ * A)
    {x X₁₁ X₁₂ X₂₂ : I.E} (h₁ : GE I g₁ X₁₁) (h₂ : GE I g₂ X₂₂)
    (h₁₂ : X₁₂ ∈ (algebraMap (𝓞 I.E) I.E).range)
    (hx : x = (q₁ : I.E) ^ 2 * X₁₁ + (q₁ : I.E) * (q₂ : I.E) * X₁₂ + (q₂ : I.E) ^ 2 * X₂₂) :
    GE I (g₁ * g₂) x := by sorry
