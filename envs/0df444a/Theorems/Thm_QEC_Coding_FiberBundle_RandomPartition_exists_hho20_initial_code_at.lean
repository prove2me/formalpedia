-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_exists_hho20_initial_code_at
-- name    : QEC.Coding.FiberBundle.RandomPartition.exists_hho20_initial_code_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:00:59.599674+00:00
-- url     : https://prove2.me/theorems/f2b5ebbd-9a48-480c-a1db-a3ff65543e2e
-- title:
--   Random Partition: exists hho20 initial code at
-- statement:
--   The concrete CSS code selected at every hierarchy index has its exact
--   block length and both pre-reduction distance lower bounds, in addition to all
--   random-base and twist-graph properties.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/InitialCode.lean#L66-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/InitialCode.lean#L66-L151

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialCode
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
open QEC.Coding.FiberBundle.RandomPartition

theorem QEC.Coding.FiberBundle.RandomPartition.exists_hho20_initial_code_at
    (s : Nat) (hs : 200 ≤ s) :
    letI : NeZero (hho20BaseScale s) :=
      ⟨by
        have := hho20_baseScale_ge_five_hundred s hs
        omega⟩
    letI : NeZero (hho20TypeCount s) :=
      ⟨hho20TypeCount_ne_zero s (by omega)⟩
    letI : NeZero (hho20FiberLength s) :=
      ⟨by
        have := hho20_fiberLength_ge s (by omega)
        omega⟩
    letI : NeZero (hho20FiberLength s - 1) :=
      ⟨by
        have := hho20_fiberLength_ge s (by omega)
        omega⟩
    ∃ (baseSample : RandomBase.Sample (hho20BaseScale s))
        (twistSample :
          RandomTwist.Sample (hho20BaseScale s)
            (hho20TypeCount s) (hho20FiberLength s)),
      RandomBase.IsFullyGood
          (Delta := hho20DegreeScale s) baseSample ∧
        TwistGraph.HasHHO20PartitionedChecks
          (hho20DegreeScale s) baseSample twistSample ∧
        TwistGraph.HasHHO20CayleySpectrum twistSample ∧
        TwistGraph.HasHHO20LocalTestability
          (hho20DegreeScale s) baseSample twistSample ∧
        Fintype.card
            (QubitIndex
              (Fin (3 * hho20BaseScale s))
              (Fin (4 * hho20BaseScale s))
              (ZMod (hho20FiberLength s * hho20FiberLength s))
              (ZMod (hho20FiberLength s * hho20FiberLength s))) =
          7 * hho20BaseScale s *
            (hho20FiberLength s * hho20FiberLength s) ∧
        CohomologyDistanceAtLeast
          (RandomTwist.fiberBundleData baseSample twistSample)
          (min
            (Fintype.card
              (ZMod (hho20FiberLength s * hho20FiberLength s)) / 2)
            ((6 * hho20BaseScale s) /
              (100000 * hho20DegreeScale s))) ∧
        HomologyDistanceAtLeast
          (RandomTwist.fiberBundleData baseSample twistSample)
          ((hho20FiberLength s * (4 * hho20BaseScale s)) /
            (5000 * hho20DegreeScale s)) ∧
        (binaryCSSCode
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).stabilizer.IsSourceValidBinary := by sorry
