-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_iteratedDeriv_scale
-- name    : PositivityTheory.SiegelWeilFormula.KFPB.iteratedDeriv_scale
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:03:15.970896+00:00
-- url     : https://prove2.me/theorems/578327e5-2114-529c-9a29-af51d947c6b3
-- title:
--   KFPB: iterated Deriv scale
-- statement:
--   The KFPB construction uses the iterated Deriv scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IteratedDerivScale.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IteratedDerivScale.lean#L9-L12

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IteratedDerivScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Nat
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFPB

theorem PositivityTheory.SiegelWeilFormula.KFPB.iteratedDeriv_scale (E : ℂ → ℂ) (hE : Differentiable ℂ E) (c : ℂ) (j : ℕ) :
    iteratedDeriv j (fun z => E (c * z)) 0 = c ^ j * iteratedDeriv j E 0 := by sorry
