-- Prove2me | Theorems.Thm_PositivityTheory_KReal_dense_countable
-- name    : PositivityTheory.KReal.dense_countable
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:14:55.170665+00:00
-- url     : https://prove2.me/theorems/de5984c0-e2c3-48e0-879b-480a18a0f12a
-- title:
--   KReal: dense countable
-- statement:
--   The KReal construction uses the dense countable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/Tensor.lean#L59-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/Tensor.lean#L59-L63

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

theorem PositivityTheory.KReal.dense_countable {V : Type} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (h : Module.rank ℂ V ≤ Cardinal.aleph0) (B : Subalgebra ℂ (Module.End ℂ V))
    (hB : ∀ N : Submodule ℂ V, (∀ b ∈ B, ∀ x ∈ N, b x ∈ N) → N = ⊥ ∨ N = ⊤)
    (f : Module.End ℂ V) (s : Finset V) : ∃ b ∈ B, ∀ m ∈ s, f m = b m := by sorry
