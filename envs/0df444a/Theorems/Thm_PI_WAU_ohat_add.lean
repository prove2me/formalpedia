-- Prove2me | Theorems.Thm_PI_WAU_ohat_add
-- name    : PI.WAU.ohat_add
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:38:53.361715+00:00
-- url     : https://prove2.me/theorems/7f7d6e5d-2efc-4ebc-a74a-8eea71debbff
-- title:
--   WAU: ohat add
-- statement:
--   The WAU construction uses the ohat add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/SmulEqAlgebraMapMul.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/SmulEqAlgebraMapMul.lean#L35-L37

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CoordTmulOneMul
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_SmulEqAlgebraMapMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped TensorProduct
variable {F : Type} [Field F] [NumberField F]

theorem PI.WAU.ohat_add {a c : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) (hc : c ∈ Ohat F) : a + c ∈ Ohat F := by sorry
