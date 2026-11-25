-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_lvA_mulVec_int
-- name    : PI.UnitaryGroupMassFormula.InHHClassFin.lvA_mulVec_int
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:39:39.265768+00:00
-- url     : https://prove2.me/theorems/29e85206-0915-44b6-8105-8650d32f4a70
-- title:
--   In HHClass Fin: lv A mul Vec int
-- statement:
--   The In HHClass Fin construction uses the lv A mul Vec int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/LevelA.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/LevelA.lean#L16-L20

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_LevelA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
variable {R : Type} [CommRing R] (S : Subring R) {n : ℕ}

theorem PI.UnitaryGroupMassFormula.InHHClassFin.lvA_mulVec_int {ι κ : Type} [Fintype κ] (M : Matrix ι κ R) (hM : ∀ i j, M i j ∈ S)
    (v : κ → R) (hv : ∀ i, v i ∈ S) : ∀ i, (M *ᵥ v) i ∈ S := by sorry
