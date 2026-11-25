-- Prove2me | Theorems.Thm_PI_FinKW_psiV_tauF
-- name    : PI.FinKW.psiV_tauF
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:32:25.475176+00:00
-- url     : https://prove2.me/theorems/2817d26e-9747-5d02-836e-612bea826c93
-- title:
--   Fin KW: psi V tau F
-- statement:
--   The Fin KW construction uses the psi V tau F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/VecVMulVec.lean#L13-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/VecVMulVec.lean#L13-L25

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_VecVMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FinKW
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
open Formalism.L2.SG.AdBridge

theorem PI.FinKW.psiV_tauF (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) :
    psiV I v (tauF I z) =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v) (AlgHom.id I.F I.E) (prF I z) := by sorry
