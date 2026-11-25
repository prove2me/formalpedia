-- Prove2me | Theorems.Thm_PI_WAU_intC_neg
-- name    : PI.WAU.intC_neg
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:55:22.804402+00:00
-- url     : https://prove2.me/theorems/96adcac6-07d3-4de1-965e-0735c383282d
-- title:
--   WAU: int C neg
-- statement:
--   The WAU construction uses the int C neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/LamAfLeOhatL.lean#L78-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/LamAfLeOhatL.lean#L78-L81

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatSmulMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_LamAfLeOhatL
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
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Formalism.MainNotions.S
open scoped TensorProduct
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}
local notation "Af" => FiniteAdeleRing (𝓞 F) F
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem PI.WAU.intC_neg {b : Module.Basis ι F E} {x : E ⊗[F] Af} (hx : IntC b x) : IntC b (-x) := by sorry
