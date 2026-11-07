-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_exists_homologous_isHorizontallyResidueNormalized
-- name    : QEC.Coding.FiberBundle.exists_homologous_isHorizontallyResidueNormalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:54:08.509967+00:00
-- url     : https://prove2.me/theorems/b01b5531-4984-4d44-bcd0-27a0df47bda8
-- title:
--   Fiber Bundle: exists homologous is Horizontally Residue Normalized
-- statement:
--   HHO20 Lemma `sliding`, with all finite choices internalized: every bundle
--   cycle has a homologous representative of no greater weight whose nonzero
--   horizontal cells all lie at fiber positions congruent to zero modulo `ell`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L4081-L4226
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L4081-L4226

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.exists_homologous_isHorizontallyResidueNormalized
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
        ).middleCycleCode.carrier) :
    ∃ z',
      z' ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier ∧
      HammingWeight z' ≤ HammingWeight z ∧
      z' + z ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier ∧
      IsHorizontallyResidueNormalized z' := by sorry
