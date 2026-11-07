-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_exists_globalSlideIterate_isHorizontallyResidueNormalized_of_connected
-- name    : QEC.Coding.FiberBundle.exists_globalSlideIterate_isHorizontallyResidueNormalized_of_connected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:54:44.283697+00:00
-- url     : https://prove2.me/theorems/7017ac20-e93a-436b-aa8f-33760f766bb7
-- title:
--   Fiber Bundle: exists global Slide Iterate is Horizontally Residue Normalized of connected
-- statement:
--   If every supported horizontal cell belongs to one support-induced cluster,
--   a finite global slide places the entire horizontal support at residue zero
--   without changing weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L4838-L4888
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L4838-L4888

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.exists_globalSlideIterate_isHorizontallyResidueNormalized_of_connected
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier)
    (root : Fin (4 * r) × ZMod (ell * ell))
    (hConnected :
      ∀ x, z (Sum.inl x) ≠ 0 →
        InSameSupportedHorizontalCluster
          baseSample twistSample z root x) :
    ∃ k,
      HammingWeight
          (globalSlideIterate baseSample twistSample z k) =
        HammingWeight z ∧
      globalSlideIterate baseSample twistSample z k + z ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier ∧
      IsHorizontallyResidueNormalized
        (globalSlideIterate baseSample twistSample z k) := by sorry
