-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitConjSum_exists_conjPt_eq_7a4df2a5a456
-- name    : P2M_GroundTheory_Heights__Heights_OrbitConjSum_exists_conjPt_eq_7a4df2a5a456
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:14:02.490243+00:00
-- url     : https://prove2.me/theorems/3ca5fc68-902e-449d-bb8f-8e927513bc03
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Conj Sum exists conj Pt eq 7a4df2a5a456: P2 M Ground Theory Heights  Heights Orbit Conj Sum exists conj Pt eq 7a4df2a5a456
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Conj Sum exists conj Pt eq 7a4df2a5a456 construction uses the P2 M Ground Theory Heights  Heights Orbit Conj Sum exists conj Pt eq 7a4df2a5a456 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitConjSumLemmas.lean#L237-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitConjSumLemmas.lean#L237-L321

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

theorem P2M_GroundTheory_Heights__Heights_OrbitConjSum_exists_conjPt_eq_7a4df2a5a456 (x : Cone n (AlgebraicClosure ℚ)) (hx : BlockNonzero x)
    (c : (k : ι) → Fin (n k + 1)) (hc : ∀ k, x k (c k) ≠ 0)
    (q : projPts (ι := blockIdx n) (orbitIdeal x)) : ∃ σ, conjPt x hx σ = q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitConjSum».«exists_conjPt_eq» := P2M_GroundTheory_Heights__Heights_OrbitConjSum_exists_conjPt_eq_7a4df2a5a456
