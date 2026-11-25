-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_locSplitP_dec
-- name    : PI.UnitaryGroupMassFormula.ScXuExists.locSplitP_dec
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:07:17.460488+00:00
-- url     : https://prove2.me/theorems/a13b962d-5cf2-5dfc-b4ad-38108edfdff0
-- title:
--   Sc Xu Exists: loc Split P dec
-- statement:
--   The Sc Xu Exists construction uses the loc Split P dec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/SplitLoc.lean#L14-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/SplitLoc.lean#L14-L37

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SplitGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_NatCastTmul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SplitLoc
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
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

theorem PI.UnitaryGroupMassFormula.ScXuExists.locSplitP_dec (I : AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) (Rf : RefData I g r k e f)
    (v : HeightOneSpectrum (𝓞 I.F)) (hsum : SumOne I v (PI.FinKW.psiV I v Rf.ew)) :
    ∃ p1 : RV I v →+* KV I v, IsAdaptedFirstProjection I v (PI.FinKW.psiV I v Rf.ew) p1 ∧
      ∀ x : RV I v, x = algebraMap (KV I v) (RV I v) (p1 x) * PI.FinKW.psiV I v Rf.ew +
        algebraMap (KV I v) (RV I v) (p1 (PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v x)) *
          PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) := by sorry
