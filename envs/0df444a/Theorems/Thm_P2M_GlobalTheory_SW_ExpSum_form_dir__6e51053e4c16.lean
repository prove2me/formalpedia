-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SW_ExpSum_form_dir__6e51053e4c16
-- name    : P2M_GlobalTheory_SW_ExpSum_form_dir__6e51053e4c16
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:09:03.23286+00:00
-- url     : https://prove2.me/theorems/e6a3e972-597d-447e-8f01-847c91d9c31c
-- title:
--   P2 M Global Theory SW Exp Sum form dir  6e51053e4c16: P2 M Global Theory SW Exp Sum form dir  6e51053e4c16
-- statement:
--   The P2 M Global Theory SW Exp Sum form dir  6e51053e4c16 construction uses the P2 M Global Theory SW Exp Sum form dir  6e51053e4c16 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsHeatThH.lean#L143-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsHeatThH.lean#L143-L150

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

theorem P2M_GlobalTheory_SW_ExpSum_form_dir__6e51053e4c16 (x : Matrix (Fin n) (Fin N) E) (τ : Ψ) (a b : Fin N) :
    form Ψ x (dir Ψ τ a b, 0, 0) = 2 * π * I * ∑ k, τ.1 (x k a) * conj (τ.1 (x k b)) := by sorry

alias «GlobalTheory».«SW».«ExpSum».«form_dir₁» := P2M_GlobalTheory_SW_ExpSum_form_dir__6e51053e4c16
