-- Prove2me | Theorems.Thm_PI_HeckeProdW_Phi_single
-- name    : PI.HeckeProdW.Phi_single
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:31:29.552793+00:00
-- url     : https://prove2.me/theorems/61d45e57-049b-4811-a1f9-1826a1c3970e
-- title:
--   Hecke Prod W: Phi single
-- statement:
--   The Hecke Prod W construction uses the Phi single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HeckeLocalProduct/PvLocalSelf.lean#L34-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HeckeLocalProduct/PvLocalSelf.lean#L34-L44

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

theorem PI.HeckeProdW.Phi_single [DecidableEq (HeightOneSpectrum (𝓞 L))] (v : HeightOneSpectrum (𝓞 L))
    (w : (v.adicCompletionIntegers L)ˣ) :
    Phi L (Pi.mulSingle v w) = localIdele L v (Units.map (v.adicCompletionIntegers L).subtype.toMonoidHom w) := by sorry
