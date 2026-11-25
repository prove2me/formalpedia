-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_stable_eval_sub
-- name    : PositivityTheory.Rg.Sw.FFTSteps.stable_eval_sub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:49:31.110153+00:00
-- url     : https://prove2.me/theorems/88bb472b-60b8-4834-9de5-fb94a57a8a27
-- title:
--   FFTSteps: stable eval sub
-- statement:
--   The FFTSteps construction uses the stable eval sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/Stable.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/Stable.lean#L10-L19

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_InvariantPolynomialEqAevalPairings
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_Stable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps

theorem PositivityTheory.Rg.Sw.FFTSteps.stable_eval_sub {ι A B : Type} [Fintype ι] (g h : Matrix ι ι ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) (p : PV ι A B) :
    eval z (sub g h p) = eval (Sum.elim (fun x : ι × A => ∑ j, g x.1 j * z (Sum.inl (j, x.2)))
      (fun y : ι × B => ∑ j, h y.1 j * z (Sum.inr (j, y.2)))) p := by sorry
