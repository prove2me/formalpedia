-- Prove2me | Theorems.Thm_P2M_PI_FinKW_smul_one_tmul__5e47ee373b19
-- name    : P2M_PI_FinKW_smul_one_tmul__5e47ee373b19
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:57:06.064939+00:00
-- url     : https://prove2.me/theorems/5d2c79c0-81e9-4301-9616-7744327cf152
-- title:
--   P2 M PI Fin KW smul one tmul  5e47ee373b19: P2 M PI Fin KW smul one tmul  5e47ee373b19
-- statement:
--   The P2 M PI Fin KW smul one tmul  5e47ee373b19 construction uses the P2 M PI Fin KW smul one tmul  5e47ee373b19 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/LocFrom.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/LocFrom.lean#L34-L40

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

theorem P2M_PI_FinKW_smul_one_tmul__5e47ee373b19 (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (r : v.adicCompletionIntegers I.F)
    (e : I.E) :
    r • ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) ⊗ₜ[I.F] e) = ((r : v.adicCompletion I.F) ⊗ₜ[I.F] e) := by sorry

alias «PI».«FinKW».«smul_one_tmul'» := P2M_PI_FinKW_smul_one_tmul__5e47ee373b19
