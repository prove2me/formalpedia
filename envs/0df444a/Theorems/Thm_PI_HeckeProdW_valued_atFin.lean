-- Prove2me | Theorems.Thm_PI_HeckeProdW_valued_atFin
-- name    : PI.HeckeProdW.valued_atFin
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:06:44.531281+00:00
-- url     : https://prove2.me/theorems/60ca363d-a640-473d-8e11-1994bd39f7d6
-- title:
--   Hecke Prod W: valued at Fin
-- statement:
--   The Hecke Prod W construction uses the valued at Fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HeckeLocalProduct/PvLocalSelf.lean#L112-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HeckeLocalProduct/PvLocalSelf.lean#L112-L114

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

theorem PI.HeckeProdW.valued_atFin (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) :
    Valued.v ((atFin v k : (v.adicCompletion L)ˣ) : v.adicCompletion L) = v.valuation L (k : L) := by sorry
