-- Prove2me | Theorems.Thm_PI_InvTopW_tmul_mem_IntAf
-- name    : PI.InvTopW.tmul_mem_IntAf
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:10:26.166284+00:00
-- url     : https://prove2.me/theorems/295fc0dc-8fe1-47ed-b4c4-8728d2737e86
-- title:
--   Inv Top W: tmul mem Int Af
-- statement:
--   The Inv Top W construction uses the tmul mem Int Af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/CoordFin.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/CoordFin.lean#L14-L24

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_LinearIndependentOneBeta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_FiniteNeighbourhoodSecond
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_CoordFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvTopW
open NumberField IsDedekindDomain Matrix Topology Filter
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge

theorem PI.InvTopW.tmul_mem_IntAf (I : AutInst) {x : I.E} (hx : x ∈ Formalism.UG.intOE I.E)
    {a : Formalism.MainNotions.S.Af I.F} (ha : a ∈ Formalism.UG.intAd I.F) :
    x ⊗ₜ[I.F] a ∈ Formalism.MainNotions.S.IntAf I.F I.E := by sorry
