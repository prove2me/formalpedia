-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_hasHHO20CayleySpectrum_of_forall_not_centeredFrequencyBad
-- name    : QEC.Coding.FiberBundle.TwistGraph.hasHHO20CayleySpectrum_of_forall_not_centeredFrequencyBad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:59:43.683757+00:00
-- url     : https://prove2.me/theorems/5a2b7fcb-db63-4272-9bf2-4ade41e381b0
-- title:
--   Twist Graph: has HHO20 Cayley Spectrum of forall not centered Frequency Bad
-- statement:
--   A simultaneous centered bound at every nonzero frequency implies the
--   exact Fourier-spectrum event required by the deterministic mixing proof.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L630-L692
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L630-L692

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod ENNReal NNReal
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSpaceChoiceValue
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSingletonClassChoiceValue

theorem QEC.Coding.FiberBundle.TwistGraph.hasHHO20CayleySpectrum_of_forall_not_centeredFrequencyBad
    {r typeCount ell : Nat}
    [NeZero ell] [NeZero (ell - 1)]
    (sample : RandomTwist.Sample r typeCount ell)
    (hEll : 100001 ≤ ell)
    (hGood :
      ∀ frequency : ZMod ell, frequency ≠ 0 →
        ¬ CenteredFrequencyBad frequency sample) :
    HasHHO20CayleySpectrum sample := by sorry
