-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_incl_mem_Lf
-- name    : PI.UnitaryGroupMassFormula.ScXuExists.incl_mem_Lf
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:42:50.801831+00:00
-- url     : https://prove2.me/theorems/af45ac3d-971a-4388-b0d5-a191e08c20f9
-- title:
--   Sc Xu Exists: incl mem Lf
-- statement:
--   The Sc Xu Exists construction uses the incl mem Lf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/NatCastTmul.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/NatCastTmul.lean#L24-L26

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_ValNatCastLtOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_NatCastTmul
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

theorem PI.UnitaryGroupMassFormula.ScXuExists.incl_mem_Lf (I : AutInst) (l : Fin I.n → I.E) (hl : l ∈ I.L) :
    (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (l i)) ∈ I.Lf := by sorry
