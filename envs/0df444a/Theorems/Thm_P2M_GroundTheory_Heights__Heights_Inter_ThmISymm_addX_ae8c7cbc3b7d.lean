-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_addX_ae8c7cbc3b7d
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_addX_ae8c7cbc3b7d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:32:29.580662+00:00
-- url     : https://prove2.me/theorems/b373724c-7e7c-5b6d-8e48-f126731f6572
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm ISymm add X ae8c7cbc3b7d: P2 M Ground Theory Heights  Heights Inter Thm ISymm add X ae8c7cbc3b7d
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm ISymm add X ae8c7cbc3b7d construction uses the P2 M Ground Theory Heights  Heights Inter Thm ISymm add X ae8c7cbc3b7d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmISymm.lean#L108-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmISymm.lean#L108-L125

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_addX_ae8c7cbc3b7d (hR : IsRFamily I) (hRS : RPositionAdd.Statement) {P : Ideal (MRing ι)} {m : ℕ}
    (hP : IsArithVar P (m + 1 + 1)) {L : Fin m → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {A C Y : HermLine ι} (hA : IsSmoothHerm A) (hC : IsSmoothHerm C) (hY : IsSmoothHerm Y) :
    I P (m + 1 + 1) (Fin.snoc (Fin.snoc L (A.tensor C)) Y) =
      I P (m + 1 + 1) (Fin.snoc (Fin.snoc L A) Y) + I P (m + 1 + 1) (Fin.snoc (Fin.snoc L C) Y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmISymm».«addX» := P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_addX_ae8c7cbc3b7d
