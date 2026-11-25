-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SW_ExpSum_form_dir__8ff127926bb4
-- name    : P2M_GlobalTheory_SW_ExpSum_form_dir__8ff127926bb4
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:09:13.664796+00:00
-- url     : https://prove2.me/theorems/4ebc6b56-e603-4350-b7c1-a2f0a4366a99
-- title:
--   P2 M Global Theory SW Exp Sum form dir  8ff127926bb4: P2 M Global Theory SW Exp Sum form dir  8ff127926bb4
-- statement:
--   The P2 M Global Theory SW Exp Sum form dir  8ff127926bb4 construction uses the P2 M Global Theory SW Exp Sum form dir  8ff127926bb4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsHeatThH.lean#L152-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsHeatThH.lean#L152-L159

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

theorem P2M_GlobalTheory_SW_ExpSum_form_dir__8ff127926bb4 (x : Matrix (Fin n) (Fin N) E) (τ : Ψ) (k : Fin n) (a : Fin N) :
    form Ψ x (0, dir Ψ τ k a, 0) = 2 * π * I * τ.1 (x k a) := by sorry

alias «GlobalTheory».«SW».«ExpSum».«form_dir₂» := P2M_GlobalTheory_SW_ExpSum_form_dir__8ff127926bb4
