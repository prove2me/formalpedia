-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_integral_mon
-- name    : PositivityTheory.Rg.Sw.FFTSteps.PosProof.integral_mon
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:41:33.856995+00:00
-- url     : https://prove2.me/theorems/8960aac6-66c0-4690-8b23-ff359fe79cae
-- title:
--   Pos Proof: integral mon
-- statement:
--   The Pos Proof construction uses the integral mon property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/IntegralMonSelf.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/IntegralMonSelf.lean#L33-L37

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

theorem PositivityTheory.Rg.Sw.FFTSteps.PosProof.integral_mon (m m' : Sg ι A B →₀ ℕ) :
    ∫ z : Sg ι A B → ℂ, mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) =
      ∏ s, ∫ w, hk (m s) (m' s) w := by sorry
