-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_iteratedDeriv_poly_real_zero
-- name    : PositivityTheory.SiegelWeilFormula.KFPB.iteratedDeriv_poly_real_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:03:24.417932+00:00
-- url     : https://prove2.me/theorems/4ceca082-3265-427a-9bb0-f97dc23831ba
-- title:
--   KFPB: iterated Deriv poly real zero
-- statement:
--   The KFPB construction uses the iterated Deriv poly real zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IteratedDerivPolyRealZero.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IteratedDerivPolyRealZero.lean#L30-L35

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

theorem PositivityTheory.SiegelWeilFormula.KFPB.iteratedDeriv_poly_real_zero (p : Polynomial ℂ) (k : ℕ) :
    iteratedDeriv k (fun t : ℝ => p.eval (t : ℂ)) 0 = (k.factorial : ℂ) * p.coeff k := by sorry
