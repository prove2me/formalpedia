-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_exists_homologous_isHorizontallyResidueNormalized_of_clusterCount_eq_one
-- name    : QEC.Coding.FiberBundle.exists_homologous_isHorizontallyResidueNormalized_of_clusterCount_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:13:31.777242+00:00
-- url     : https://prove2.me/theorems/12dfb9f8-e17d-4b87-8fea-103536fee8f7
-- title:
--   Fiber Bundle: exists homologous is Horizontally Residue Normalized of cluster Count eq one
-- statement:
--   The one-cluster terminal case of HHO20 Lemma `sliding`: a cycle with nonzero
--   base projection and cluster count one has a homologous, equal-weight
--   representative whose horizontal support is at residue zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L4895-L4933
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L4895-L4933

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.exists_homologous_isHorizontallyResidueNormalized_of_clusterCount_eq_one
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
    (hProjection : homologyBaseProjection z ≠ 0)
    (hCount :
      horizontalClusterCount baseSample twistSample z = 1) :
    ∃ z',
      HammingWeight z' = HammingWeight z ∧
      z' + z ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier ∧
      IsHorizontallyResidueNormalized z' := by sorry
