-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_recR_comp_perm_30ab7bd66c6c
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_recR_comp_perm_30ab7bd66c6c
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:26:40.145797+00:00
-- url     : https://prove2.me/theorems/b37a2c15-f8b4-44b3-948d-bf78d9f5ec4b
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm ISymm rec R comp perm 30ab7bd66c6c: P2 M Ground Theory Heights  Heights Inter Thm ISymm rec R comp perm 30ab7bd66c6c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm ISymm rec R comp perm 30ab7bd66c6c construction uses the P2 M Ground Theory Heights  Heights Inter Thm ISymm rec R comp perm 30ab7bd66c6c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmISymm.lean#L41-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmISymm.lean#L41-L59

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_recR_comp_perm_30ab7bd66c6c
    (hEU : ∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement (ZMod p) ι)
    (hSy : ∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.AI.I1.SymmStatement (ZMod p) ι)
    (hGN : ReciprocityTheory.ChartRestriction.G.AI.I1.GeoNumStatement ι) (hFC : FibreCompStatement)
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) {P : Ideal (MRing ι)} {n : ℕ}
    (hP : IsArithVar P (n + 1)) (L : Fin n → HermLine ι) (B : HermLine ι) {s : MRing ι}
    (hs : IsSectionOn P B s) (τ : Equiv.Perm (Fin n))
    (hI : ∀ W, IsArithVar W n → I W n (L ∘ τ) = I W n L) :
    recR I P (L ∘ τ) B s = recR I P L B s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmISymm».«recR_comp_perm» := P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_recR_comp_perm_30ab7bd66c6c
