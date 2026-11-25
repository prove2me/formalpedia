-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitConjSum_conjPt_eq_iff_c88f58f58153
-- name    : P2M_GroundTheory_Heights__Heights_OrbitConjSum_conjPt_eq_iff_c88f58f58153
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:14:24.574918+00:00
-- url     : https://prove2.me/theorems/1cec3957-da81-423c-848f-4115aa159ce8
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Conj Sum conj Pt eq iff c88f58f58153: P2 M Ground Theory Heights  Heights Orbit Conj Sum conj Pt eq iff c88f58f58153
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Conj Sum conj Pt eq iff c88f58f58153 construction uses the P2 M Ground Theory Heights  Heights Orbit Conj Sum conj Pt eq iff c88f58f58153 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitConjSumLemmas.lean#L211-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitConjSumLemmas.lean#L211-L235

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

theorem P2M_GroundTheory_Heights__Heights_OrbitConjSum_conjPt_eq_iff_c88f58f58153 (x : Cone n (AlgebraicClosure ℚ)) (hx : BlockNonzero x)
    (c : (k : ι) → Fin (n k + 1)) (hc : ∀ k, x k (c k) ≠ 0) (σ σ' : coordField x →+* ℂ) :
    conjPt x hx σ = conjPt x hx σ' ↔ ∀ p, σ (ratio x c p) = σ' (ratio x c p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitConjSum».«conjPt_eq_iff» := P2M_GroundTheory_Heights__Heights_OrbitConjSum_conjPt_eq_iff_c88f58f58153
