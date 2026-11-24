-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocallyPrincipalCoprimeAlt_finite_maximal_of_ne_zero_b905aca18701
-- name    : P2M_GroundTheory_Heights__Heights_LocallyPrincipalCoprimeAlt_finite_maximal_of_ne_zero_b905aca18701
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:26:16.206144+00:00
-- url     : https://prove2.me/theorems/fb1d8ab0-0a9a-4be3-aaec-0264bf785669
-- title:
--   P2 M Ground Theory Heights  Heights Locally Principal Coprime Alt finite maximal of ne zero b905aca18701: P2 M Ground Theory Heights  Heights Locally Principal Coprime Alt finite maximal of ne zero b9
-- statement:
--   The P2 M Ground Theory Heights  Heights Locally Principal Coprime Alt finite maximal of ne zero b905aca18701 construction uses the P2 M Ground Theory Heights  Heights Locally Principal Coprime Alt finite maximal of ne zero b905aca18701 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLocallyPrincipalCoprime.lean#L11-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLocallyPrincipalCoprime.lean#L11-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLocallyPrincipalCoprime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLocallyPrincipalCoprime
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
open GroundTheory.Heights₂.Heights.LocallyPrincipalCoprimeAlt
variable {L : Type} [Field L]

theorem P2M_GroundTheory_Heights__Heights_LocallyPrincipalCoprimeAlt_finite_maximal_of_ne_zero_b905aca18701 [CharZero L] (B : Subring L) [Module.Finite ℤ B] {s : B} (hs : s ≠ 0) :
    Set.Finite {m : Ideal B | m.IsMaximal ∧ s ∈ m} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LocallyPrincipalCoprimeAlt».«finite_maximal_of_ne_zero» := P2M_GroundTheory_Heights__Heights_LocallyPrincipalCoprimeAlt_finite_maximal_of_ne_zero_b905aca18701
