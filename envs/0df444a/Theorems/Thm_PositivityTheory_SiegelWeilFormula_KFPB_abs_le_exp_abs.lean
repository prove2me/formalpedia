-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_abs_le_exp_abs
-- name    : PositivityTheory.SiegelWeilFormula.KFPB.abs_le_exp_abs
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:03:40.127185+00:00
-- url     : https://prove2.me/theorems/ecd72ee6-8680-4a0f-8353-cb6a4abbd8ab
-- title:
--   KFPB: abs le exp abs
-- statement:
--   The KFPB construction uses the abs le exp abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IntegrableRexpLin.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IntegrableRexpLin.lean#L25-L27

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

theorem PositivityTheory.SiegelWeilFormula.KFPB.abs_le_exp_abs (x : ℝ) : |x| ≤ Real.exp |x| := by sorry
