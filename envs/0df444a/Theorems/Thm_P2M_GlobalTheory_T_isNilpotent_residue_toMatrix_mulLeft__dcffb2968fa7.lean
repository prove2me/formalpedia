-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_isNilpotent_residue_toMatrix_mulLeft__dcffb2968fa7
-- name    : P2M_GlobalTheory_T_isNilpotent_residue_toMatrix_mulLeft__dcffb2968fa7
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:10:26.973247+00:00
-- url     : https://prove2.me/theorems/087c0eee-b212-4b40-a94b-1615bbf4bc31
-- title:
--   P2 M Global Theory T is Nilpotent residue to Matrix mul Left  dcffb2968fa7: P2 M Global Theory T is Nilpotent residue to Matrix mul Left  dcffb2968fa7
-- statement:
--   The P2 M Global Theory T is Nilpotent residue to Matrix mul Left  dcffb2968fa7 construction uses the P2 M Global Theory T is Nilpotent residue to Matrix mul Left  dcffb2968fa7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsNilpotentResidueToMatrixMulLeftStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsNilpotentResidueToMatrixMulLeftStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsNilpotentResidueToMatrixMulLeft
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsNilpotentResidueToMatrixMulLeftStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_isNilpotent_residue_toMatrix_mulLeft__dcffb2968fa7 : ∀ (R S : Type) [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [Algebra R S] (n : ℕ) (b : Module.Basis (Fin n) R S) (t : S), t ∈ IsLocalRing.maximalIdeal S → IsNilpotent ((LinearMap.toMatrix b b (LinearMap.mulLeft R t)).map (IsLocalRing.residue R)) := by sorry

alias «GlobalTheory».«T».«isNilpotent_residue_toMatrix_mulLeft'» := P2M_GlobalTheory_T_isNilpotent_residue_toMatrix_mulLeft__dcffb2968fa7
