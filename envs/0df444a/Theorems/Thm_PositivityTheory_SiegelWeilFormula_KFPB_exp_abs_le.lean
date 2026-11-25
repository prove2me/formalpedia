-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_exp_abs_le
-- name    : PositivityTheory.SiegelWeilFormula.KFPB.exp_abs_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:03:35.871288+00:00
-- url     : https://prove2.me/theorems/a80da07a-366b-4ffa-bbd2-be18750d24db
-- title:
--   KFPB: exp abs le
-- statement:
--   The KFPB construction uses the exp abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IntegrableRexpLin.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IntegrableRexpLin.lean#L29-L32

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrableRexpLin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped SchwartzMap InnerProductSpace
open MeasureTheory Complex
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFPB
variable {ι : Type} [Fintype ι]

theorem PositivityTheory.SiegelWeilFormula.KFPB.exp_abs_le (a s : ℝ) : Real.exp (a * |s|) ≤ Real.exp (a * s) + Real.exp (-(a * s)) := by sorry
