-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_selectedReferenceMarginal_eq_rightMarginal_transport
-- name    : QEC.Bounds.BPTEntropy.selectedReferenceMarginal_eq_rightMarginal_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:27:11.821622+00:00
-- url     : https://prove2.me/theorems/f4402b3c-46d0-4ba6-b106-ca2a3bcc1460
-- title:
--   BPTEntropy: selected Reference Marginal eq right Marginal transport
-- statement:
--   The selected/reference state from #412 is the right marginal after its
--   explicit transport into `(M tensor Ref) tensor complement`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L126-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L126-L133

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
open QEC.Bounds.BPTEntropy
open Semantics
open Semantics.DensityOperator
universe u

theorem QEC.Bounds.BPTEntropy.selectedReferenceMarginal_eq_rightMarginal_transport
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (S : QuditSubsystem q) (Ref : Type u)
    [NormedAddCommGroup Ref] [InnerProductSpace Complex Ref] [FiniteQuantumSystem Ref]
    (omega : DensityOperator (CompositeSystem (Qudit.QuditRegister q) Ref)) :
    S.selectedReferenceMarginal Ref omega =
      rightMarginal ((S.selectedReferenceTransport Ref).conjDensity omega) := by sorry
