-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_finite_bad
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.finite_bad
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:41:13.89206+00:00
-- url     : https://prove2.me/theorems/86c59a33-71dd-4837-9ef4-f38349ccb6f3
-- title:
--   Ad Index Eq: finite bad
-- statement:
--   The Ad Index Eq construction uses the finite bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/Reduce.lean#L67-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/Reduce.lean#L67-L89

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

theorem PI.UnitaryGroupMassFormula.AdIndexEq.finite_bad (I : AutInst) (x : I.Gf) :
    {v | matV I v (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∉ Kv I v}.Finite := by sorry
