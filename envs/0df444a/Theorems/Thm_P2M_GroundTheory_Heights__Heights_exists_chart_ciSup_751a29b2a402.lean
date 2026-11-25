-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_chart_ciSup_751a29b2a402
-- name    : P2M_GroundTheory_Heights__Heights_exists_chart_ciSup_751a29b2a402
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:46:20.924799+00:00
-- url     : https://prove2.me/theorems/04820a2e-c4f5-4720-9a68-3aeb32699d92
-- title:
--   P2 M Ground Theory Heights  Heights exists chart ci Sup 751a29b2a402: P2 M Ground Theory Heights  Heights exists chart ci Sup 751a29b2a402
-- statement:
--   The P2 M Ground Theory Heights  Heights exists chart ci Sup 751a29b2a402 construction uses the P2 M Ground Theory Heights  Heights exists chart ci Sup 751a29b2a402 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCenterDivSuppLemmas.lean#L71-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCenterDivSuppLemmas.lean#L71-L80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenter
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PHeightRecR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterMemIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCenterDivSuppLemmas
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_exists_chart_ciSup_751a29b2a402 (x : Cone n (AlgebraicClosure ℚ)) (hx : BlockNonzero x)
    (v : FinitePlace (coordField x)) :
    ∃ c : (k : ι) → Fin (n k + 1), ∀ k, v (coordVec x k (c k)) = ⨆ i, v (coordVec x k i) ∧
      0 < ⨆ i, v (coordVec x k i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_chart_ciSup» := P2M_GroundTheory_Heights__Heights_exists_chart_ciSup_751a29b2a402
