-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_mem_Uv_iff
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.mem_Uv_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:39:28.200584+00:00
-- url     : https://prove2.me/theorems/01389af2-ff3e-47ba-b39f-6850c535bf52
-- title:
--   Ad Index Eq: mem Uv iff
-- statement:
--   The Ad Index Eq construction uses the mem Uv iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/CompactLocalGlobal.lean#L96-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/CompactLocalGlobal.lean#L96-L98

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

theorem PI.UnitaryGroupMassFormula.AdIndexEq.mem_Uv_iff (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (g : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) :
    g ∈ Uv I v ↔ Formalism.UG.cT (sigV I v) g.val * I.J.map (inclV I v) * g.val = I.J.map (inclV I v) := by sorry
