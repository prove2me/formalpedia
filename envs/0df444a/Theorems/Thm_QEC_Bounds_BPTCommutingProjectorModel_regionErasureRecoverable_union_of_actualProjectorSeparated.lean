-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionErasureRecoverable_union_of_actualProjectorSeparated
-- name    : QEC.Bounds.BPTCommutingProjectorModel.regionErasureRecoverable_union_of_actualProjectorSeparated
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T08:13:54.901325+00:00
-- url     : https://prove2.me/theorems/dd07f9a9-438b-4618-a6e4-7647484bd23c
-- title:
--   BPTCommuting Projector Model: region Erasure Recoverable union of actual Projector Separated
-- statement:
--   The BPT separated-union lemma (`2Dgeneral_codes08.tex`, lines 698--727).
--   `ActualProjectorSeparated` refers to the supports of the concrete commuting
--   projectors supplied by #378, exactly as in the source.  It first removes the
--   overlap `left ∩ right` from `left`: actual support separation preserves the
--   projector-defined boundary and its external part, while erasure recoverability
--   is monotone under this shrinking.  The resulting two regions are disjoint, so
--   the proof follows the source's rank-one disentangling calculation through the
--   retained #388 final-assembly witness, then uses the finite-qudit
--   no-information/recovery equivalence from #402.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Bound.lean#L36-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Bound.lean#L36-L74

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Factorizations_Factorization
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Separation
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Bound
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.regionErasureRecoverable_union_of_actualProjectorSeparated
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hseparated : M.ActualProjectorSeparated left right)
    (hleft : M.RegionErasureRecoverable left)
    (hright : M.RegionErasureRecoverable right)
    (hexternal : M.RegionErasureRecoverable (M.externalBoundary left)) :
    M.RegionErasureRecoverable (left ∪ right) := by sorry
