-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_addX_sec_833eae78c407
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_addX_sec_833eae78c407
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:24.693364+00:00
-- url     : https://prove2.me/theorems/1d226b81-8b89-4e69-ac05-ac49d4264342
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm ISymm add X sec 833eae78c407: P2 M Ground Theory Heights  Heights Inter Thm ISymm add X sec 833eae78c407
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm ISymm add X sec 833eae78c407 construction uses the P2 M Ground Theory Heights  Heights Inter Thm ISymm add X sec 833eae78c407 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmISymm.lean#L97-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmISymm.lean#L97-L106

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_addX_sec_833eae78c407 (hR : IsRFamily I) (hRS : RPositionAdd.Statement) {P : Ideal (MRing ι)} {m : ℕ}
    (hP : IsArithVar P (m + 1 + 1)) {L : Fin m → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {A C Y : HermLine ι} (hA : IsSmoothHerm A) (hC : IsSmoothHerm C) (hY : IsSmoothHerm Y) {y : MRing ι}
    (hy : IsSectionOn P Y y) :
    I P (m + 1 + 1) (Fin.snoc (Fin.snoc L (A.tensor C)) Y) =
      I P (m + 1 + 1) (Fin.snoc (Fin.snoc L A) Y) + I P (m + 1 + 1) (Fin.snoc (Fin.snoc L C) Y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmISymm».«addX_sec» := P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_addX_sec_833eae78c407
