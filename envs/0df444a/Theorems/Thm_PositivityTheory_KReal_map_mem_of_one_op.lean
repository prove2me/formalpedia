-- Prove2me | Theorems.Thm_PositivityTheory_KReal_map_mem_of_one_op
-- name    : PositivityTheory.KReal.map_mem_of_one_op
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:14:00.288244+00:00
-- url     : https://prove2.me/theorems/e19d16f7-3593-568e-8bd7-2eab2b64b923
-- title:
--   KReal: map mem of one op
-- statement:
--   The KReal construction uses the map mem of one op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/Tensor.lean#L107-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/Tensor.lean#L107-L127

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_TensorIrr
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Algebraic.LinearIndependent
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Cardinality
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SpectrumNonemptyOfCountableRank
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_Tensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.KReal
variable {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]

theorem PositivityTheory.KReal.map_mem_of_one_op [Fintype ι] (N : Submodule ℂ (PiTensorProduct ℂ M))
    (hN : ∀ i (f : Module.End ℂ (M i)), ∀ x ∈ N, one_op i f x ∈ N)
    (f : ∀ i, Module.End ℂ (M i)) (x : PiTensorProduct ℂ M) (hx : x ∈ N) : PiTensorProduct.map f x ∈ N := by sorry
