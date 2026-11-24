-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_vecV_mL
-- name    : PI.UnitaryGroupMassFormula.ScXuExists.vecV_mL
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:31:55.320806+00:00
-- url     : https://prove2.me/theorems/8294d1dc-4e9b-425e-a768-360cf4a6e1e7
-- title:
--   Sc Xu Exists: vec V m L
-- statement:
--   The Sc Xu Exists construction uses the vec V m L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/ValNatCastLtOne.lean#L62-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/ValNatCastLtOne.lean#L62-L83

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_CompactLocalGlobal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_ValNatCastLtOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

theorem PI.UnitaryGroupMassFormula.ScXuExists.vecV_mL (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (m : ℕ) (x : Fin I.n → I.E ⊗[I.F] Af I.F)
    (hx : x ∈ mL I m) :
    ∃ w ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)), PI.FinKW.vecV I v x = (m : RV I v) • w := by sorry
