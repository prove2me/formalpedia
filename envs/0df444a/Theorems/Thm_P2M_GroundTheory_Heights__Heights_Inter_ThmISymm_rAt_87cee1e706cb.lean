-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_rAt_87cee1e706cb
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_rAt_87cee1e706cb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:55.238952+00:00
-- url     : https://prove2.me/theorems/7f22f4c5-2596-431e-9ee8-eda441619688
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm ISymm r At 87cee1e706cb: P2 M Ground Theory Heights  Heights Inter Thm ISymm r At 87cee1e706cb
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm ISymm r At 87cee1e706cb construction uses the P2 M Ground Theory Heights  Heights Inter Thm ISymm r At 87cee1e706cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmISymm.lean#L65-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmISymm.lean#L65-L69

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_rAt_87cee1e706cb (hR : IsRFamily I) {P : Ideal (MRing ι)} {n : ℕ} {L : Fin n → HermLine ι} {A : HermLine ι}
    {s : MRing ι} (hP : IsArithVar P (n + 1)) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hs : IsSectionOn P A s) : I P (n + 1) (Fin.snoc L A) = recR I P L A s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmISymm».«rAt» := P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_rAt_87cee1e706cb
