-- Prove2me | Theorems.Thm_PI_GGConvScalarW_isUni_sgn_conj
-- name    : PI.GGConvScalarW.isUni_sgn_conj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:56.510814+00:00
-- url     : https://prove2.me/theorems/48b5300e-3974-454f-9dbf-a006a65cf3c5
-- title:
--   GGConv Scalar W: is Uni sgn conj
-- statement:
--   The GGConv Scalar W construction uses the is Uni sgn conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/SuperdiagSgnConj.lean#L156-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/SuperdiagSgnConj.lean#L156-L158

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_SuperdiagSgnConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
noncomputable section
open Classical
open PI PI.GGConvScalarW
open Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ}

theorem PI.GGConvScalarW.isUni_sgn_conj {u : GL (Fin k) F} (h : IsUni k u) : IsUni k (sgn k * u * sgn k) := by sorry
