-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_cubN
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_cubN
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:50.182804+00:00
-- url     : https://prove2.me/theorems/0fcdc951-ed4a-460e-bba9-3f86aefcc607
-- title:
--   Tor: exists cub N
-- statement:
--   The Tor construction uses the exists cub N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/CubeVal.lean#L190-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/CubeVal.lean#L190-L219

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_cubN {T : Over S} (a m x : T ⟶ G) (k : ℕ) :
    ∃ t : LB.Gen (LB.LinComb L.L (K := Fin 8) ![(a * m ^ k * x).left, (a * m ^ k).left, (a * x).left, a.left,
        (m * x).left, m.left, x.left, (1 : T ⟶ G).left] ![1, -1, -1, 1, -k, k, k, -k]), t.IsGen ∧
      ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good L.L z J →
        val t ρ.left z J = cubN (cubV c z J) k (ρ ≫ a) (ρ ≫ m) (ρ ≫ x) := by sorry
