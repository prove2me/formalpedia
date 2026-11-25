-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_geoNum_comp_perm_a68f58b0bb57
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_geoNum_comp_perm_a68f58b0bb57
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:02:47.337829+00:00
-- url     : https://prove2.me/theorems/ee330073-8093-540d-97b9-87fac0be736c
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm ISymm geo Num comp perm a68f58b0bb57: P2 M Ground Theory Heights  Heights Inter Thm ISymm geo Num comp perm a68f58b0bb57
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm ISymm geo Num comp perm a68f58b0bb57 construction uses the P2 M Ground Theory Heights  Heights Inter Thm ISymm geo Num comp perm a68f58b0bb57 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmISymm.lean#L27-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmISymm.lean#L27-L39

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_geoNum_comp_perm_a68f58b0bb57
    (hEU : ∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement (ZMod p) ι)
    (hSy : ∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.AI.I1.SymmStatement (ZMod p) ι)
    (hGN : ReciprocityTheory.ChartRestriction.G.AI.I1.GeoNumStatement ι) (hFC : FibreCompStatement)
    {P : Ideal (MRing ι)} {n : ℕ} {A : HermLine ι} {s : MRing ι} {W : Ideal (MRing ι)}
    (hP : IsArithVar P (n + 1)) (hs : IsSectionOn P A s) (hW : W ∈ divSupp P s)
    (hv : ¬ IsHorizontal W) (a : Fin n → K → ℤ) (τ : Equiv.Perm (Fin n)) :
    geoNum n W (a ∘ τ) = geoNum n W a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmISymm».«geoNum_comp_perm» := P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_geoNum_comp_perm_a68f58b0bb57
