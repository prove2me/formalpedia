-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitConjSum_restrict_eq_iff_7898508957a0
-- name    : P2M_GroundTheory_Heights__Heights_OrbitConjSum_restrict_eq_iff_7898508957a0
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:14:32.103732+00:00
-- url     : https://prove2.me/theorems/08d05497-47ff-428b-b7b8-b3a85bdf4ac6
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Conj Sum restrict eq iff 7898508957a0: P2 M Ground Theory Heights  Heights Orbit Conj Sum restrict eq iff 7898508957a0
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Conj Sum restrict eq iff 7898508957a0 construction uses the P2 M Ground Theory Heights  Heights Orbit Conj Sum restrict eq iff 7898508957a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitConjSumLemmas.lean#L188-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitConjSumLemmas.lean#L188-L203

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
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_OrbitConjSum_restrict_eq_iff_7898508957a0 (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (σ σ' : coordField x →+* ℂ) :
    σ.comp (algebraMap (ratioField x c) (coordField x)) =
        σ'.comp (algebraMap (ratioField x c) (coordField x)) ↔
      ∀ p, σ (ratio x c p) = σ' (ratio x c p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitConjSum».«restrict_eq_iff» := P2M_GroundTheory_Heights__Heights_OrbitConjSum_restrict_eq_iff_7898508957a0
