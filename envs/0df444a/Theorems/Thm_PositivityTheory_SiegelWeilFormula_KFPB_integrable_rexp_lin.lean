-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_integrable_rexp_lin
-- name    : PositivityTheory.SiegelWeilFormula.KFPB.integrable_rexp_lin
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:03:36.0433+00:00
-- url     : https://prove2.me/theorems/8ef1df00-ce7e-4132-9d14-d166295a6b46
-- title:
--   KFPB: integrable rexp lin
-- statement:
--   The KFPB construction uses the integrable rexp lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IntegrableRexpLin.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IntegrableRexpLin.lean#L14-L23

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

theorem PositivityTheory.SiegelWeilFormula.KFPB.integrable_rexp_lin (c : ℝ) (hc : 0 < c) (a : ℝ) (ξ : EuclideanSpace ℝ ι) :
    Integrable (fun u : EuclideanSpace ℝ ι => Real.exp (-(c * ‖u‖ ^ 2) + a * ⟪ξ, u⟫_ℝ)) := by sorry
