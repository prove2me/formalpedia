-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_swap_sec_0a1f9b163397
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_swap_sec_0a1f9b163397
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:01:41.943403+00:00
-- url     : https://prove2.me/theorems/ec238d5a-7cba-4594-be1f-13b99cde062c
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm ISymm swap sec 0a1f9b163397: P2 M Ground Theory Heights  Heights Inter Thm ISymm swap sec 0a1f9b163397
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm ISymm swap sec 0a1f9b163397 construction uses the P2 M Ground Theory Heights  Heights Inter Thm ISymm swap sec 0a1f9b163397 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmISymm.lean#L127-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmISymm.lean#L127-L134

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsWellDefined
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChoice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmISymm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.ThmISymm
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_swap_sec_0a1f9b163397 (hR : IsRFamily I) (hSwap : Swap.Statement) {P : Ideal (MRing ι)} {m : ℕ}
    (hP : IsArithVar P (m + 1 + 1)) {L : Fin m → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {X Y : HermLine ι} (hX : IsSmoothHerm X) (hY : IsSmoothHerm Y) {x y : MRing ι}
    (hx : IsSectionOn P X x) (hy : IsSectionOn P Y y) (hd : ∀ W, W ∈ divSupp P y → W ∉ divSupp P x) :
    I P (m + 1 + 1) (Fin.snoc (Fin.snoc L X) Y) = I P (m + 1 + 1) (Fin.snoc (Fin.snoc L Y) X) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmISymm».«swap_sec» := P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_swap_sec_0a1f9b163397
