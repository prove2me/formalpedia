-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_iteratedDeriv_line
-- name    : PositivityTheory.SiegelWeilFormula.KFPB.iteratedDeriv_line
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:03:38.955266+00:00
-- url     : https://prove2.me/theorems/6d3b6cc0-6d9c-55dc-a3d7-7cfd6376844f
-- title:
--   KFPB: iterated Deriv line
-- statement:
--   The KFPB construction uses the iterated Deriv line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IteratedDerivPolyRealZero.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IteratedDerivPolyRealZero.lean#L9-L16

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

theorem PositivityTheory.SiegelWeilFormula.KFPB.iteratedDeriv_line {N : ℕ} (K : EuclideanSpace ℝ ι → ℂ) (hK : ContDiff ℝ N K) (ξ : EuclideanSpace ℝ ι)
    {k : ℕ} (hk : k ≤ N) :
    iteratedDeriv k (fun t : ℝ => K (t • ξ)) 0 = iteratedFDeriv ℝ k K 0 (fun _ => ξ) := by sorry
