-- Prove2me | Theorems.Thm_PI_WAU_exists_lower
-- name    : PI.WAU.exists_lower
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:51:21.738712+00:00
-- url     : https://prove2.me/theorems/8d12dd4b-1c11-52ba-90d5-679a263c4724
-- title:
--   WAU: exists lower
-- statement:
--   The WAU construction uses the exists lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ExistsNatSmulMem.lean#L31-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ExistsNatSmulMem.lean#L31-L68

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_SmulEqAlgebraMapMul
import Definitions.Def_Lemmata_GeneralBFactThirdMore_Key
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatSmulMem
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

theorem PI.WAU.exists_lower (b : Module.Basis ι F E) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ d : ℕ, 0 < d ∧ ∀ y : Fin n → E ⊗[F] Af, (∀ j, IntC b (y j)) → d • y ∈ lamAf (F := F) L := by sorry
