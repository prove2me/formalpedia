-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_mon_prod
-- name    : PositivityTheory.Rg.Sw.FFTSteps.PosProof.mon_prod
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:42:05.795331+00:00
-- url     : https://prove2.me/theorems/131c8d20-8762-454c-922b-d1ea7eee22b2
-- title:
--   Pos Proof: mon prod
-- statement:
--   The Pos Proof construction uses the mon prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/IntegralMonSelf.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/IntegralMonSelf.lean#L21-L24

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ContinuousPhi
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralMonSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Module
open scoped ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.PosProof
variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]

theorem PositivityTheory.Rg.Sw.FFTSteps.PosProof.mon_prod (m m' : Sg ι A B →₀ ℕ) (z : Sg ι A B → ℂ) :
    mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) = ∏ s, hk (m s) (m' s) (z s) := by sorry
