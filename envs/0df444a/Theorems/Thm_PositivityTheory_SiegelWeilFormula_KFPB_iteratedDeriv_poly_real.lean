-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_iteratedDeriv_poly_real
-- name    : PositivityTheory.SiegelWeilFormula.KFPB.iteratedDeriv_poly_real
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:03:17.869864+00:00
-- url     : https://prove2.me/theorems/3126c31e-4f9d-412f-9e6f-301e1c71f1a7
-- title:
--   KFPB: iterated Deriv poly real
-- statement:
--   The KFPB construction uses the iterated Deriv poly real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IteratedDerivPolyRealZero.lean#L18-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IteratedDerivPolyRealZero.lean#L18-L28

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IteratedDerivPolyRealZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFPB
variable {ι : Type} [Fintype ι]

theorem PositivityTheory.SiegelWeilFormula.KFPB.iteratedDeriv_poly_real (p : Polynomial ℂ) (k : ℕ) :
    iteratedDeriv k (fun t : ℝ => p.eval (t : ℂ)) = fun t : ℝ => (Polynomial.derivative^[k] p).eval (t : ℂ) := by sorry
