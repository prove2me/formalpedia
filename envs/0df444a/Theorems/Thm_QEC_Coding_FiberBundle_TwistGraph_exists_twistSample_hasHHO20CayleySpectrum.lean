-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_exists_twistSample_hasHHO20CayleySpectrum
-- name    : QEC.Coding.FiberBundle.TwistGraph.exists_twistSample_hasHHO20CayleySpectrum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:00:02.973958+00:00
-- url     : https://prove2.me/theorems/4a6ade26-6cf0-4f63-a247-4d1462d56483
-- title:
--   Twist Graph: exists twist Sample has HHO20 Cayley Spectrum
-- statement:
--   The random nonzero shifts contain a deterministic sample satisfying the
--   complete HHO20 Cayley-spectrum event.  No spectral certificate is supplied
--   by the caller.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L697-L733
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean#L697-L733

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod ENNReal NNReal
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSpaceChoiceValue
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSingletonClassChoiceValue

theorem QEC.Coding.FiberBundle.TwistGraph.exists_twistSample_hasHHO20CayleySpectrum
    (r typeCount ell : Nat)
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (hEll : 100001 ≤ ell)
    (hTypeCount :
      (40000000000 : Real) * Real.log (ell : Real) ≤
        (typeCount : Real)) :
    ∃ sample : RandomTwist.Sample r typeCount ell,
      HasHHO20CayleySpectrum sample := by sorry
