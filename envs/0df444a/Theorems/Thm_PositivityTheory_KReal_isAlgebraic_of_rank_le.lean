-- Prove2me | Theorems.Thm_PositivityTheory_KReal_isAlgebraic_of_rank_le
-- name    : PositivityTheory.KReal.isAlgebraic_of_rank_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:19:29.435875+00:00
-- url     : https://prove2.me/theorems/c26e31b2-26ce-5f08-b957-c1fca9af3aaa
-- title:
--   KReal: is Algebraic of rank le
-- statement:
--   The KReal construction uses the is Algebraic of rank le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/Tensor.lean#L14-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/Tensor.lean#L14-L36

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

theorem PositivityTheory.KReal.isAlgebraic_of_rank_le {D : Type} [DivisionRing D] [Algebra ℂ D]
    (h : Module.rank ℂ D ≤ Cardinal.aleph0) (x : D) : IsAlgebraic ℂ x := by sorry
