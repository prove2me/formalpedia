-- Prove2me | Theorems.Thm_PI_ScRefExists_GWG_hG_comb
-- name    : PI.ScRefExists.GWG.hG_comb
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:25:15.591029+00:00
-- url     : https://prove2.me/theorems/0e385874-cfeb-5c18-b7ab-f93717993180
-- title:
--   GWG: h G comb
-- statement:
--   The GWG construction uses the h G comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/GWGlue.lean#L57-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/GWGlue.lean#L57-L62

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

theorem PI.ScRefExists.GWG.hG_comb (q₁ q₂ : ℤ) (x₁ x₂ y₁ y₂ : Fin I.n → I.E) :
    hG I (q₁ • x₁ + q₂ • x₂) (q₁ • y₁ + q₂ • y₂) =
      (q₁ : I.E) ^ 2 * hG I x₁ y₁ + (q₁ : I.E) * (q₂ : I.E) * (hG I x₁ y₂ + hG I x₂ y₁) +
        (q₂ : I.E) ^ 2 * hG I x₂ y₂ := by sorry
