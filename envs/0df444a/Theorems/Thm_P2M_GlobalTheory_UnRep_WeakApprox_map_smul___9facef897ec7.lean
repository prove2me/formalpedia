-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnRep_WeakApprox_map_smul___9facef897ec7
-- name    : P2M_GlobalTheory_UnRep_WeakApprox_map_smul___9facef897ec7
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:21:31.324271+00:00
-- url     : https://prove2.me/theorems/9d032f1f-1182-4a23-bbab-dcf692dd4bbb
-- title:
--   P2 M Global Theory Un Rep Weak Approx map smul   9facef897ec7: P2 M Global Theory Un Rep Weak Approx map smul   9facef897ec7
-- statement:
--   The P2 M Global Theory Un Rep Weak Approx map smul   9facef897ec7 construction uses the P2 M Global Theory Un Rep Weak Approx map smul   9facef897ec7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnitaryGroupWeakApproximationAtPrimes.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnitaryGroupWeakApproximationAtPrimes.lean#L47-L50

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

theorem P2M_GlobalTheory_UnRep_WeakApprox_map_smul___9facef897ec7 {K R : Type} [CommRing K] [CommRing R] (ι : K →+* R) {n : ℕ} (r : K)
    (A : Matrix (Fin n) (Fin n) K) : (r • A).map ι = ι r • A.map ι := by sorry

alias «GlobalTheory».«UnRep».«WeakApprox».«map_smul''» := P2M_GlobalTheory_UnRep_WeakApprox_map_smul___9facef897ec7
