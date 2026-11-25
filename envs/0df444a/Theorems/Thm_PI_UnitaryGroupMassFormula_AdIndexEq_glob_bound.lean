-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_glob_bound
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.glob_bound
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:47:40.167827+00:00
-- url     : https://prove2.me/theorems/f399d736-d047-5cfc-80a9-4adbe243a74c
-- title:
--   Ad Index Eq: glob bound
-- statement:
--   The Ad Index Eq construction uses the glob bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/Reduce.lean#L13-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/Reduce.lean#L13-L24

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LiftMatMapSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Reduce
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S

theorem PI.UnitaryGroupMassFormula.AdIndexEq.glob_bound (I : AutInst) (x : I.Gf) :
    ∃ N : ℕ, 0 < N ∧ (∀ w ∈ I.Lf, N • (I.fmat x *ᵥ w) ∈ I.Lf) ∧
      (∀ w ∈ I.Lf, N • (I.fmat x⁻¹ *ᵥ w) ∈ I.Lf) := by sorry
