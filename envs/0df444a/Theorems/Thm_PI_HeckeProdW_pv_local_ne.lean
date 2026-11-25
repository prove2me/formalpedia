-- Prove2me | Theorems.Thm_PI_HeckeProdW_pv_local_ne
-- name    : PI.HeckeProdW.pv_local_ne
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:31:22.832417+00:00
-- url     : https://prove2.me/theorems/051bbcf6-9b53-48bc-932a-f9e7755765ef
-- title:
--   Hecke Prod W: pv local ne
-- statement:
--   The Hecke Prod W construction uses the pv local ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HeckeLocalProduct/PvLocalSelf.lean#L85-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HeckeLocalProduct/PvLocalSelf.lean#L85-L90

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

theorem PI.HeckeProdW.pv_local_ne (v v' : HeightOneSpectrum (𝓞 L)) (h : v' ≠ v) (x : (v.adicCompletion L)ˣ) :
    pv v' (localIdele L v x) = 1 := by sorry
