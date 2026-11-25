-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitConjSum_exists_int_mul_3eff43bbc16e
-- name    : P2M_GroundTheory_Heights__Heights_OrbitConjSum_exists_int_mul_3eff43bbc16e
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:15:10.220245+00:00
-- url     : https://prove2.me/theorems/e7eb9152-8212-4265-b077-3eee44a97444
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Conj Sum exists int mul 3eff43bbc16e: P2 M Ground Theory Heights  Heights Orbit Conj Sum exists int mul 3eff43bbc16e
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Conj Sum exists int mul 3eff43bbc16e construction uses the P2 M Ground Theory Heights  Heights Orbit Conj Sum exists int mul 3eff43bbc16e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitConjSumLemmas.lean#L90-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitConjSumLemmas.lean#L90-L109

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitConjSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitConjSumLemmas
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitConjSum
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_OrbitConjSum_exists_int_mul_3eff43bbc16e {κ : Type*} (F : MvPolynomial κ ℚ) :
    ∃ (N : ℤ) (P : MvPolynomial κ ℤ), N ≠ 0 ∧ map (Int.castRingHom ℚ) P = C (N : ℚ) * F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitConjSum».«exists_int_mul» := P2M_GroundTheory_Heights__Heights_OrbitConjSum_exists_int_mul_3eff43bbc16e
