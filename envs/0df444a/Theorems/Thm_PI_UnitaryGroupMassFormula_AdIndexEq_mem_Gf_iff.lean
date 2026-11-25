-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_mem_Gf_iff
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.mem_Gf_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:48:06.206385+00:00
-- url     : https://prove2.me/theorems/27b3b1cf-2b22-5cbf-a150-91b4da126ded
-- title:
--   Ad Index Eq: mem Gf iff
-- statement:
--   The Ad Index Eq construction uses the mem Gf iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/CompactLocalGlobal.lean#L100-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/CompactLocalGlobal.lean#L100-L103

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocInj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocLift
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_CompactLocalGlobal
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
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S

theorem PI.UnitaryGroupMassFormula.AdIndexEq.mem_Gf_iff (I : AutInst) (g : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    g ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F) ↔
      Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) g.val * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
        g.val = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by sorry
