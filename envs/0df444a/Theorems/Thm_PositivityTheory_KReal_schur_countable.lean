-- Prove2me | Theorems.Thm_PositivityTheory_KReal_schur_countable
-- name    : PositivityTheory.KReal.schur_countable
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:50:37.407071+00:00
-- url     : https://prove2.me/theorems/4476f541-395e-47a4-b420-71ad9d6e9f96
-- title:
--   KReal: schur countable
-- statement:
--   The KReal construction uses the schur countable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/Tensor.lean#L38-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/Tensor.lean#L38-L57

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

theorem PositivityTheory.KReal.schur_countable {B V : Type} [Ring B] [Algebra ℂ B] [AddCommGroup V] [Module ℂ V] [Module B V]
    [IsScalarTower ℂ B V] [IsSimpleModule B V] (h : Module.rank ℂ V ≤ Cardinal.aleph0) :
    Function.Surjective (algebraMap ℂ (Module.End B V)) := by sorry
