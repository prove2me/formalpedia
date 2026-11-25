-- Prove2me | Theorems.Thm_PI_InvTopW_tmul_natCast_mul
-- name    : PI.InvTopW.tmul_natCast_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:08:53.423603+00:00
-- url     : https://prove2.me/theorems/26e25020-6d01-4441-b57d-903aa6c9494f
-- title:
--   Inv Top W: tmul nat Cast mul
-- statement:
--   The Inv Top W construction uses the tmul nat Cast mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/CoordFin.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/CoordFin.lean#L26-L28

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

theorem PI.InvTopW.tmul_natCast_mul (I : AutInst) (N : ℕ) (b : I.E) (z : Formalism.MainNotions.S.Af I.F) :
    b ⊗ₜ[I.F] ((N : Formalism.MainNotions.S.Af I.F) * z) = (N : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * (b ⊗ₜ[I.F] z) := by sorry
