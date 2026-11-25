-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SW_ExpSum_line__191ffd3dba45
-- name    : P2M_GlobalTheory_SW_ExpSum_line__191ffd3dba45
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:09:05.890007+00:00
-- url     : https://prove2.me/theorems/ac0f4136-56f7-42ca-91c8-71873fd03179
-- title:
--   P2 M Global Theory SW Exp Sum line  191ffd3dba45: P2 M Global Theory SW Exp Sum line  191ffd3dba45
-- statement:
--   The P2 M Global Theory SW Exp Sum line  191ffd3dba45 construction uses the P2 M Global Theory SW Exp Sum line  191ffd3dba45 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsHeatThH.lean#L172-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsHeatThH.lean#L172-L174

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatThH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ExpSum
variable {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
open Classical

theorem P2M_GlobalTheory_SW_ExpSum_line__191ffd3dba45 (Z : CF Ψ N N) (z z' : CF Ψ n N) (τ : Ψ) (a b : Fin N) (s : ℂ) :
    (Z, z, z') + s • ((dir Ψ τ a b, 0, 0) : CF Ψ N N × CF Ψ n N × CF Ψ n N) =
      (Z + s • dir Ψ τ a b, z, z') := by sorry

alias «GlobalTheory».«SW».«ExpSum».«line₁» := P2M_GlobalTheory_SW_ExpSum_line__191ffd3dba45
