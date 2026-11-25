-- Prove2me | Theorems.Thm_PI_HeckeProdW_pv_diag
-- name    : PI.HeckeProdW.pv_diag
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:31:18.69217+00:00
-- url     : https://prove2.me/theorems/37374972-7594-46bd-81a9-2961beed69e7
-- title:
--   Hecke Prod W: pv diag
-- statement:
--   The Hecke Prod W construction uses the pv diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HeckeLocalProduct/PvLocalSelf.lean#L110-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HeckeLocalProduct/PvLocalSelf.lean#L110-L110

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

theorem PI.HeckeProdW.pv_diag (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : pv v (diagUnits L k) = (atFin v k : v.adicCompletion L) := by sorry
