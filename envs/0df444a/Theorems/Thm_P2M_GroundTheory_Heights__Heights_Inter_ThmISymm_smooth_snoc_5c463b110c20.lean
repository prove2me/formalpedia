-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_smooth_snoc_5c463b110c20
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_smooth_snoc_5c463b110c20
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:25.076674+00:00
-- url     : https://prove2.me/theorems/5086493c-ce1f-4dd0-8c09-8913514124ff
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm ISymm smooth snoc 5c463b110c20: P2 M Ground Theory Heights  Heights Inter Thm ISymm smooth snoc 5c463b110c20
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm ISymm smooth snoc 5c463b110c20 construction uses the P2 M Ground Theory Heights  Heights Inter Thm ISymm smooth snoc 5c463b110c20 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmISymm.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmISymm.lean#L20-L25

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_smooth_snoc_5c463b110c20 {n : ℕ} {L : Fin n → HermLine ι} {X : HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    (hX : IsSmoothHerm X) : ∀ j, IsSmoothHerm ((Fin.snoc L X : Fin (n + 1) → HermLine ι) j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmISymm».«smooth_snoc» := P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_smooth_snoc_5c463b110c20
