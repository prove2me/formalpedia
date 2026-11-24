-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitConjSum_conj_chart_ne_zero_edf026820d33
-- name    : P2M_GroundTheory_Heights__Heights_OrbitConjSum_conj_chart_ne_zero_edf026820d33
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:25:50.033112+00:00
-- url     : https://prove2.me/theorems/9261c1de-fd1f-4252-9462-7ec813b4fb31
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Conj Sum conj chart ne zero edf026820d33: P2 M Ground Theory Heights  Heights Orbit Conj Sum conj chart ne zero edf026820d33
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Conj Sum conj chart ne zero edf026820d33 construction uses the P2 M Ground Theory Heights  Heights Orbit Conj Sum conj chart ne zero edf026820d33 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitConjSumLemmas.lean#L181-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitConjSumLemmas.lean#L181-L184

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

theorem P2M_GroundTheory_Heights__Heights_OrbitConjSum_conj_chart_ne_zero_edf026820d33 (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) (σ : coordField x →+* ℂ) (k : ι) :
    σ (coordVec x k (c k)) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitConjSum».«conj_chart_ne_zero» := P2M_GroundTheory_Heights__Heights_OrbitConjSum_conj_chart_ne_zero_edf026820d33
