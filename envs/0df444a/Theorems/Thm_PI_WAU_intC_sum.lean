-- Prove2me | Theorems.Thm_PI_WAU_intC_sum
-- name    : PI.WAU.intC_sum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:43:50.458221+00:00
-- url     : https://prove2.me/theorems/db6e7ae2-bf3e-4455-bd6a-0b647f5a2776
-- title:
--   WAU: int C sum
-- statement:
--   The WAU construction uses the int C sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/SmulEqAlgebraMapMul.lean#L108-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/SmulEqAlgebraMapMul.lean#L108-L112

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
variable {E : Type} [Field E] [NumberField E] [Algebra F E]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
local notation "Af" => FiniteAdeleRing (𝓞 F) F
variable {b}

theorem PI.WAU.intC_sum {κ : Type*} (s : Finset κ) {f : κ → E ⊗[F] Af} (hf : ∀ i ∈ s, IntC b (f i)) :
    IntC b (∑ i ∈ s, f i) := by sorry
