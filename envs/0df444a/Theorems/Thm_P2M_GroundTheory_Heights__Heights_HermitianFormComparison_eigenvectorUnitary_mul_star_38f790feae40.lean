-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianFormComparison_eigenvectorUnitary_mul_star_38f790feae40
-- name    : P2M_GroundTheory_Heights__Heights_HermitianFormComparison_eigenvectorUnitary_mul_star_38f790feae40
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:08:00.549259+00:00
-- url     : https://prove2.me/theorems/f8d69f81-e9ed-4172-bd87-74053d7b0724
-- title:
--   P2 M Ground Theory Heights  Heights Hermitian Form Comparison eigenvector Unitary mul star 38f790feae40: P2 M Ground Theory Heights  Heights Hermitian Form Comparison eigenvector Unitary mul star 38f7
-- statement:
--   The P2 M Ground Theory Heights  Heights Hermitian Form Comparison eigenvector Unitary mul star 38f790feae40 construction uses the P2 M Ground Theory Heights  Heights Hermitian Form Comparison eigenvector Unitary mul star 38f790feae40 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PHermFormCompare.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PHermFormCompare.lean#L41-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
open scoped ComplexOrder
open GroundTheory.Heights₂.Heights.HermitianFormComparison

theorem P2M_GroundTheory_Heights__Heights_HermitianFormComparison_eigenvectorUnitary_mul_star_38f790feae40 {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermitianFormComparison».«eigenvectorUnitary_mul_star» := P2M_GroundTheory_Heights__Heights_HermitianFormComparison_eigenvectorUnitary_mul_star_38f790feae40
