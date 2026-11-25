-- Prove2me | Theorems.Thm_PI_HeckeProdW_locK_eq
-- name    : PI.HeckeProdW.locK_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:31:19.096423+00:00
-- url     : https://prove2.me/theorems/71464d1e-bccd-45f4-ae10-63aef9ad1cfb
-- title:
--   Hecke Prod W: loc K eq
-- statement:
--   The Hecke Prod W construction uses the loc K eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HeckeLocalProduct/PvLocalSelf.lean#L116-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HeckeLocalProduct/PvLocalSelf.lean#L116-L134

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_Kernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_PvLocalSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host RestrictedProduct
open PI PI.HeckeProdW
variable {L : Type} [Field L] [NumberField L]

theorem PI.HeckeProdW.locK_eq (χ : HChar L) {v : HeightOneSpectrum (𝓞 L)} (h : χ.UnrAt v) (k : Lˣ) :
    χ.locK v k = χ.val v ^ ordF v k := by sorry
