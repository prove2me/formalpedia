-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_lastFix_396ad53668d1
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_lastFix_396ad53668d1
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:24:08.341714+00:00
-- url     : https://prove2.me/theorems/0d56d104-f992-48a2-ac87-77e5b09edbea
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm ISymm last Fix 396ad53668d1: P2 M Ground Theory Heights  Heights Inter Thm ISymm last Fix 396ad53668d1
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm ISymm last Fix 396ad53668d1 construction uses the P2 M Ground Theory Heights  Heights Inter Thm ISymm last Fix 396ad53668d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmISymm.lean#L71-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmISymm.lean#L71-L95

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_lastFix_396ad53668d1
    (hEU : ∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement (ZMod p) ι)
    (hSy : ∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.AI.I1.SymmStatement (ZMod p) ι)
    (hGN : ReciprocityTheory.ChartRestriction.G.AI.I1.GeoNumStatement ι) (hFC : FibreCompStatement)
    (hR : IsRFamily I) {P : Ideal (MRing ι)} {m : ℕ} (hP : IsArithVar P (m + 1 + 1))
    (ih : ∀ W, IsArithVar W (m + 1) → ∀ L : Fin (m + 1) → HermLine ι, (∀ j, IsSmoothHerm (L j)) →
      ∀ τ : Equiv.Perm (Fin (m + 1)), I W (m + 1) (L ∘ τ) = I W (m + 1) L)
    (L : Fin (m + 1) → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) (A : HermLine ι) (hA : IsSmoothHerm A)
    (τ : Equiv.Perm (Fin (m + 1))) :
    I P (m + 1 + 1) (Fin.snoc (L ∘ τ) A) = I P (m + 1 + 1) (Fin.snoc L A) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmISymm».«lastFix» := P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_lastFix_396ad53668d1
