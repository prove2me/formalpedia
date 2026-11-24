-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjChowNonzero_aeval_smul_of_isHomogeneous_95fca94e9459
-- name    : P2M_GroundTheory_Heights__Heights_ProjChowNonzero_aeval_smul_of_isHomogeneous_95fca94e9459
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:21.84871+00:00
-- url     : https://prove2.me/theorems/6ef732ec-ac08-4b47-9595-96d5178e5a6a
-- title:
--   P2 M Ground Theory Heights  Heights Proj Chow Nonzero aeval smul of is Homogeneous 95fca94e9459: P2 M Ground Theory Heights  Heights Proj Chow Nonzero aeval smul of is Homogeneous 95fca94e9459
-- statement:
--   The P2 M Ground Theory Heights  Heights Proj Chow Nonzero aeval smul of is Homogeneous 95fca94e9459 construction uses the P2 M Ground Theory Heights  Heights Proj Chow Nonzero aeval smul of is Homogeneous 95fca94e9459 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjChowNonzero.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjChowNonzero.lean#L14-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjChowNonzero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjChowNonzero
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ProjChowNonzero

theorem P2M_GroundTheory_Heights__Heights_ProjChowNonzero_aeval_smul_of_isHomogeneous_95fca94e9459 {Ω : Type*} [Field Ω] [Algebra ℂ Ω] {n m : ℕ}
    {φ : MvPolynomial (Fin n) ℂ} (hφ : φ.IsHomogeneous m) (c : Ω) (x : Fin n → Ω) :
    aeval (c • x) φ = c ^ m * aeval x φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjChowNonzero».«aeval_smul_of_isHomogeneous» := P2M_GroundTheory_Heights__Heights_ProjChowNonzero_aeval_smul_of_isHomogeneous_95fca94e9459
