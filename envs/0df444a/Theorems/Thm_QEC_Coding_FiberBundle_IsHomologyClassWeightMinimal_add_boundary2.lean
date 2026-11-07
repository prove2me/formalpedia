-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_IsHomologyClassWeightMinimal_add_boundary2
-- name    : QEC.Coding.FiberBundle.IsHomologyClassWeightMinimal.add_boundary2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:54:00.104645+00:00
-- url     : https://prove2.me/theorems/5e18695b-4124-4c57-9890-b9a542443ad2
-- title:
--   Is Homology Class Weight Minimal: add boundary2
-- statement:
--   Equal-weight addition of a boundary preserves class-weight minimality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3910-L3937
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3910-L3937

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.IsHomologyClassWeightMinimal.add_boundary2
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hMinimal :
      IsHomologyClassWeightMinimal baseSample twistSample z)
    (c : Word (ZMod 2)
      (C2Index (Fin (4 * r)) (ZMod (ell * ell))))
    (hWeight :
      HammingWeight
          (z + boundary2
            (RandomTwist.fiberBundleData baseSample twistSample) c) =
        HammingWeight z) :
    IsHomologyClassWeightMinimal baseSample twistSample
      (z + boundary2
        (RandomTwist.fiberBundleData baseSample twistSample) c) := by sorry
