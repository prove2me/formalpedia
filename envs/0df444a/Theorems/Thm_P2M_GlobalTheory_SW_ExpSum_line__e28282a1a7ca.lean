-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SW_ExpSum_line__e28282a1a7ca
-- name    : P2M_GlobalTheory_SW_ExpSum_line__e28282a1a7ca
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:08:53.669516+00:00
-- url     : https://prove2.me/theorems/10f71352-493c-4af3-bead-61195068274d
-- title:
--   P2 M Global Theory SW Exp Sum line  e28282a1a7ca: P2 M Global Theory SW Exp Sum line  e28282a1a7ca
-- statement:
--   The P2 M Global Theory SW Exp Sum line  e28282a1a7ca construction uses the P2 M Global Theory SW Exp Sum line  e28282a1a7ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsHeatThH.lean#L179-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsHeatThH.lean#L179-L180

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

theorem P2M_GlobalTheory_SW_ExpSum_line__e28282a1a7ca (Z : CF Ψ N N) (z z' v : CF Ψ n N) (s : ℂ) :
    (Z, z, z') + s • ((0, 0, v) : CF Ψ N N × CF Ψ n N × CF Ψ n N) = (Z, z, z' + s • v) := by sorry

alias «GlobalTheory».«SW».«ExpSum».«line₃» := P2M_GlobalTheory_SW_ExpSum_line__e28282a1a7ca
