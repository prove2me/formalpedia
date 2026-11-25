-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SW_ExpSum_form_dir__9c9d997b7777
-- name    : P2M_GlobalTheory_SW_ExpSum_form_dir__9c9d997b7777
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:09:40.712249+00:00
-- url     : https://prove2.me/theorems/6f94473e-925c-4d1e-89b8-8c201d2a6be3
-- title:
--   P2 M Global Theory SW Exp Sum form dir  9c9d997b7777: P2 M Global Theory SW Exp Sum form dir  9c9d997b7777
-- statement:
--   The P2 M Global Theory SW Exp Sum form dir  9c9d997b7777 construction uses the P2 M Global Theory SW Exp Sum form dir  9c9d997b7777 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsHeatThH.lean#L161-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsHeatThH.lean#L161-L168

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

theorem P2M_GlobalTheory_SW_ExpSum_form_dir__9c9d997b7777 (x : Matrix (Fin n) (Fin N) E) (τ : Ψ) (k : Fin n) (a : Fin N) :
    form Ψ x (0, 0, dir Ψ τ k a) = 2 * π * I * conj (τ.1 (x k a)) := by sorry

alias «GlobalTheory».«SW».«ExpSum».«form_dir₃» := P2M_GlobalTheory_SW_ExpSum_form_dir__9c9d997b7777
