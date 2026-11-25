-- Prove2me | Theorems.Thm_PositivityTheory_KReal_one_op_tprod
-- name    : PositivityTheory.KReal.one_op_tprod
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:14:39.280617+00:00
-- url     : https://prove2.me/theorems/87c15e07-421e-4c12-8c7f-7a20a518d722
-- title:
--   KReal: one op tprod
-- statement:
--   The KReal construction uses the one op tprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/Tensor.lean#L72-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/Tensor.lean#L72-L79

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

theorem PositivityTheory.KReal.one_op_tprod (i : ι) (f : Module.End ℂ (M i)) (x : ∀ j, M j) :
    one_op i f (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ (Function.update x i (f (x i))) := by sorry
