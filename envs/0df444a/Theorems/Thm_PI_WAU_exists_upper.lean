-- Prove2me | Theorems.Thm_PI_WAU_exists_upper
-- name    : PI.WAU.exists_upper
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:44:18.560538+00:00
-- url     : https://prove2.me/theorems/349a1cf8-1825-5ea4-ab31-951a16db755c
-- title:
--   WAU: exists upper
-- statement:
--   The WAU construction uses the exists upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/LamAfLeOhatL.lean#L83-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/LamAfLeOhatL.lean#L83-L130

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

theorem PI.WAU.exists_upper (b : Module.Basis ι F E) (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) :
    ∃ D : ℕ, 0 < D ∧ ∀ y ∈ lamAf (F := F) L, ∀ j, IntC b (D • y j) := by sorry
