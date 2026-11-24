-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitConjSum_blockDeg_le_9e02025f8eb2
-- name    : P2M_GroundTheory_Heights__Heights_OrbitConjSum_blockDeg_le_9e02025f8eb2
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:24:34.87348+00:00
-- url     : https://prove2.me/theorems/d4adf91c-524e-490a-af96-91dac98e622b
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Conj Sum block Deg le 9e02025f8eb2: P2 M Ground Theory Heights  Heights Orbit Conj Sum block Deg le 9e02025f8eb2
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Conj Sum block Deg le 9e02025f8eb2 construction uses the P2 M Ground Theory Heights  Heights Orbit Conj Sum block Deg le 9e02025f8eb2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitConjSumLemmas.lean#L116-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitConjSumLemmas.lean#L116-L121

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
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_OrbitConjSum_blockDeg_le_9e02025f8eb2 (P : MvPolynomial (Coord n) ℤ) {m : Coord n →₀ ℕ} (hm : m ∈ P.support)
    (k : ι) : ∑ i, m ⟨k, i⟩ ≤ P.totalDegree := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitConjSum».«blockDeg_le» := P2M_GroundTheory_Heights__Heights_OrbitConjSum_blockDeg_le_9e02025f8eb2
