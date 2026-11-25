-- Prove2me | Theorems.Thm_PI_FinKW_psiV_entry
-- name    : PI.FinKW.psiV_entry
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:31:41.878147+00:00
-- url     : https://prove2.me/theorems/e36e8919-a5ab-4738-969f-f40ab36a683a
-- title:
--   Fin KW: psi V entry
-- statement:
--   The Fin KW construction uses the psi V entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/LocFrom.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/LocFrom.lean#L29-L32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocFrom
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

theorem PI.FinKW.psiV_entry (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (a : Formalism.MainNotions.S.Af I.F) (e : I.E) :
    psiV I v (((1 : I.E) ⊗ₜ[I.F] a) * (e ⊗ₜ[I.F] (1 : Formalism.MainNotions.S.Af I.F))) =
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v a) ⊗ₜ[I.F] e := by sorry
