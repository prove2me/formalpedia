-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_Gl_not_mem_of_coprime
-- name    : PI.UnitaryGroupMassFormula.ScXuExists.Gl.not_mem_of_coprime
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:18:59.226139+00:00
-- url     : https://prove2.me/theorems/690743b9-32fc-4366-a105-b18604c7dd62
-- title:
--   Gl: not mem of coprime
-- statement:
--   The Gl construction uses the not mem of coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/GlueHoldsVar.lean#L41-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/GlueHoldsVar.lean#L41-L50

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Reduce
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocInj
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_GlueHoldsVar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists PI.UnitaryGroupMassFormula.ScXuExists.Gl
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists PI.UnitaryGroupMassFormula.AdIndexEq

theorem PI.UnitaryGroupMassFormula.ScXuExists.Gl.not_mem_of_coprime {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {m g : ℕ} (h : Nat.Coprime m g) (hg : (g : 𝓞 F) ∈ v.asIdeal) : (m : 𝓞 F) ∉ v.asIdeal := by sorry
