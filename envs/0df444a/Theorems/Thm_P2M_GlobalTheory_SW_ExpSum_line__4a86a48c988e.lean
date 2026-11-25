-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SW_ExpSum_line__4a86a48c988e
-- name    : P2M_GlobalTheory_SW_ExpSum_line__4a86a48c988e
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:08:59.961596+00:00
-- url     : https://prove2.me/theorems/642803cf-07aa-4f25-a95b-b48f0d925806
-- title:
--   P2 M Global Theory SW Exp Sum line  4a86a48c988e: P2 M Global Theory SW Exp Sum line  4a86a48c988e
-- statement:
--   The P2 M Global Theory SW Exp Sum line  4a86a48c988e construction uses the P2 M Global Theory SW Exp Sum line  4a86a48c988e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsHeatThH.lean#L176-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsHeatThH.lean#L176-L177

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

theorem P2M_GlobalTheory_SW_ExpSum_line__4a86a48c988e (Z : CF Ψ N N) (z z' v : CF Ψ n N) (s : ℂ) :
    (Z, z, z') + s • ((0, v, 0) : CF Ψ N N × CF Ψ n N × CF Ψ n N) = (Z, z + s • v, z') := by sorry

alias «GlobalTheory».«SW».«ExpSum».«line₂» := P2M_GlobalTheory_SW_ExpSum_line__4a86a48c988e
