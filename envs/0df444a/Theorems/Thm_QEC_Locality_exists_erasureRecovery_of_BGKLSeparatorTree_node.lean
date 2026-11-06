-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_of_BGKLSeparatorTree_node
-- name    : QEC.Locality.exists_erasureRecovery_of_BGKLSeparatorTree_node
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:34:58.796204+00:00
-- url     : https://prove2.me/theorems/adb55ac8-63ef-470b-ae7a-08407a9e5bf0
-- title:
--   Locality: exists erasure Recovery of BGKLSeparator Tree node
-- statement:
--   Structural recovery induction on the constructed tree.  Leaves invoke semantic
--   distance (#363); branches combine the two decoupled children (#373), correct a
--   distance-small boundary/separator buffer, expand across that buffer (#377), and
--   finally shrink to the parent vertex set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L567-L690
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L567-L690

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Locality.exists_erasureRecovery_of_BGKLSeparatorTree_node
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) (hd : 0 < d)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    {beta exponent : ℝ}
    (hProfile : P.AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound beta exponent)
    {root : Finset ι} (globalTree : BGKLSeparatorTree P d root)
    (hSmall : (root.card : ℝ) ≤ Real.rpow
      (bgklSmallBoundaryEpsilon beta exponent * d) exponent⁻¹)
    (hRootBoundary : 4 * (fixedGeneratorOuterBoundaryFinset P root).card ≤ d)
    {vertices : Finset ι} (subtree : BGKLSeparatorTree P d vertices)
    {ancestors : List (Finset ι)}
    (hPosition : globalTree.IsNode subtree ancestors) :
    ∃ recovery : QuantumChannel (finiteSubsystemOfFinset vertices).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (finiteSubsystemOfFinset vertices).complementSystem P.semanticCode
        (finiteSubsystemOfFinset vertices).erasureChannelFromRegister recovery := by sorry
