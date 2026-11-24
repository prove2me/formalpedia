-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnRep_WeakApprox_map_inv__258392d9c0ad
-- name    : P2M_GlobalTheory_UnRep_WeakApprox_map_inv__258392d9c0ad
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:21:50.62535+00:00
-- url     : https://prove2.me/theorems/c6e0d1b6-2d79-4859-a483-27cd2a7b39ac
-- title:
--   P2 M Global Theory Un Rep Weak Approx map inv  258392d9c0ad: P2 M Global Theory Un Rep Weak Approx map inv  258392d9c0ad
-- statement:
--   The P2 M Global Theory Un Rep Weak Approx map inv  258392d9c0ad construction uses the P2 M Global Theory Un Rep Weak Approx map inv  258392d9c0ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnitaryGroupWeakApproximationAtPrimes.lean#L42-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnitaryGroupWeakApproximationAtPrimes.lean#L42-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CayleyTransformUnitarySkewInvolutiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdelicUnitaryScalingUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsInverseOneAddPreservingAdelicCompletionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalMatrixApproxAdeleLinearMapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryGroupWeakApproximationAtPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.WeakApprox

theorem P2M_GlobalTheory_UnRep_WeakApprox_map_inv__258392d9c0ad {K R : Type} [CommRing K] [CommRing R] (ι : K →+* R) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hA : IsUnit A.det) : (A.map ι)⁻¹ = A⁻¹.map ι := by sorry

alias «GlobalTheory».«UnRep».«WeakApprox».«map_inv'» := P2M_GlobalTheory_UnRep_WeakApprox_map_inv__258392d9c0ad
