-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_recursion_cover_erasure_coordinates
-- name    : QEC.Bounds.BPTCommutingProjectorModel.recursion_cover_erasure_coordinates
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T06:29:16.653399+00:00
-- url     : https://prove2.me/theorems/547860a6-5626-4eed-b7f2-0b43ea641f18
-- title:
--   BPTCommuting Projector Model: recursion cover erasure coordinates
-- statement:
--   The physical cover erasure, transported by its concrete complement
--   factorization, is exactly the `A tensor D` coordinate obtained by tracing the
--   literal `B` and `C` factors.  This is the bridge that prevents the recursion
--   argument from silently replacing a physical erasure by a set-theoretic one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/BlockRecursion.lean#L856-L1044
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/BlockRecursion.lean#L856-L1044

import Definitions.Def_QEC_Bounds_BPTDisentangling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open QEC.Bounds.BPTCommutingProjectorModel
open Classical
open Semantics
open Semantics.DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem QEC.Bounds.BPTCommutingProjectorModel.recursion_cover_erasure_coordinates
    (M : BPTCommutingProjectorModel L kappa)
    (region inside outside : Finset L.Site)
    (hinside : inside ⊆ region) (houtside : outside ⊆ regionᶜ)
    (rho : Operator L.Register) :
    let A := M.regionSubsystem (region \ inside)
    let BC := M.regionSubsystem (inside ∪ outside)
    let hdisjoint : Disjoint A.selected BC.selected := by
      rw [Finset.disjoint_left]
      intro site hA hBC
      rcases Finset.mem_union.mp hBC with hinsideSite | houtsideSite
      · exact (Finset.mem_sdiff.mp hA).2 hinsideSite
      · exact (Finset.mem_compl.mp (houtside houtsideSite)) (Finset.mem_sdiff.mp hA).1
    (BPTEntropy.QuditSubsystem.complementBACFactorization A BC hdisjoint).conjOperator
      (BC.erasureChannelFromRegister rho) =
      traceBCToAD A.selectedSystem
        ((M.regionSubsystem (region \ inside)).additionalRetainedSystem
          (M.regionSubsystem region))
        ((M.regionSubsystem region).additionalRetainedSystem
          (recursionABC M region inside outside))
        (recursionABC M region inside outside).complementSystem
        ((recursionFourFactorTransport M region inside outside hinside).conjOperator rho) := by sorry
