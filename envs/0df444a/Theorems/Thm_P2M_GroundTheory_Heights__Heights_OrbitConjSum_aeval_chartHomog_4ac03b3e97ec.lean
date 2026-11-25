-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitConjSum_aeval_chartHomog_4ac03b3e97ec
-- name    : P2M_GroundTheory_Heights__Heights_OrbitConjSum_aeval_chartHomog_4ac03b3e97ec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:13:21.953623+00:00
-- url     : https://prove2.me/theorems/98f681f5-7256-45a2-b0a7-f4492e7a8ce5
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Conj Sum aeval chart Homog 4ac03b3e97ec: P2 M Ground Theory Heights  Heights Orbit Conj Sum aeval chart Homog 4ac03b3e97ec
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Conj Sum aeval chart Homog 4ac03b3e97ec construction uses the P2 M Ground Theory Heights  Heights Orbit Conj Sum aeval chart Homog 4ac03b3e97ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitConjSumLemmas.lean#L136-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitConjSumLemmas.lean#L136-L163

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

theorem P2M_GroundTheory_Heights__Heights_OrbitConjSum_aeval_chartHomog_4ac03b3e97ec {F : Type*} [Field F] (c : (k : ι) → Fin (n k + 1))
    (P : MvPolynomial (Coord n) ℤ) (w : Coord n → F) (hw : ∀ k, w ⟨k, c k⟩ ≠ 0) :
    aeval w (chartHomog c P) =
      (∏ k, w ⟨k, c k⟩ ^ P.totalDegree) * aeval (fun p ↦ w p / w ⟨p.1, c p.1⟩) P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitConjSum».«aeval_chartHomog» := P2M_GroundTheory_Heights__Heights_OrbitConjSum_aeval_chartHomog_4ac03b3e97ec
