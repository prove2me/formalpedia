-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_BridgeInvAlg_matEq_of_inj
-- name    : PI.UnitaryGroupMassFormula.BridgeInvAlg.matEq_of_inj
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:31:59.273495+00:00
-- url     : https://prove2.me/theorems/2f7e388c-1213-47d1-bd16-57ad7f5e4cef
-- title:
--   Bridge Inv Alg: mat Eq of inj
-- statement:
--   The Bridge Inv Alg construction uses the mat Eq of inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantAlgebraComparison/MapThetaEq.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantAlgebraComparison/MapThetaEq.lean#L13-L22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantAlgebraComparison_BridgeHomFormula
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantAlgebraComparison_MapThetaEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BridgeInvAlg
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge

theorem PI.UnitaryGroupMassFormula.BridgeInvAlg.matEq_of_inj (hi : ThetaInj) (I : AutInst)
    {A B : Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E)}
    (hv : ∀ v, A.map (thetaV I v) = B.map (thetaV I v)) (hf : A.map (tauF I) = B.map (tauF I)) :
    A = B := by sorry
