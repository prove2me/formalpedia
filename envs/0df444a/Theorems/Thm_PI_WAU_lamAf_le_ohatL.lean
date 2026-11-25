-- Prove2me | Theorems.Thm_PI_WAU_lamAf_le_ohatL
-- name    : PI.WAU.lamAf_le_ohatL
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:43:39.62875+00:00
-- url     : https://prove2.me/theorems/6a997933-de84-46f7-87cc-4d5f0a5de36a
-- title:
--   WAU: lam Af le ohat L
-- statement:
--   The WAU construction uses the lam Af le ohat L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/LamAfLeOhatL.lean#L59-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/LamAfLeOhatL.lean#L59-L69

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

theorem PI.WAU.lamAf_le_ohatL (L : Submodule (𝓞 E) (Fin n → E)) {y : Fin n → E ⊗[F] Af}
    (hy : y ∈ lamAf (F := F) L) : y ∈ ohatL (F := F) L := by sorry
