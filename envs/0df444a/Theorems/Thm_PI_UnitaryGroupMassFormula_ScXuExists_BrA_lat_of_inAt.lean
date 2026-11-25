-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_lat_of_inAt
-- name    : PI.UnitaryGroupMassFormula.ScXuExists.BrA.lat_of_inAt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T06:04:21.746305+00:00
-- url     : https://prove2.me/theorems/920a91e2-4d94-46e7-994b-13ab934a2322
-- title:
--   Br A: lat of in At
-- statement:
--   The Br A construction uses the lat of in At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/LocalDataSatisfyLinearHypotheses.lean#L17-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/LocalDataSatisfyLinearHypotheses.lean#L17-L27

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondCoordinateVectorMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocalDataSatisfyLinearHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists PI.UnitaryGroupMassFormula.ScXuExists.BrA
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.ScXuExists
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

theorem PI.UnitaryGroupMassFormula.ScXuExists.BrA.lat_of_inAt (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) {g : ℕ} (hv : (g : 𝓞 I.F) ∈ v.asIdeal)
    (x : VA I) (hx : InAt I g 1 x) :
    PI.FinKW.vecV I v x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by sorry
