-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HDiscLat_lattice_main
-- name    : ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.lattice_main
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:00:11.844816+00:00
-- url     : https://prove2.me/theorems/7395fd41-1026-4d68-b177-8e6907ff5157
-- title:
--   HDisc Lat: lattice main
-- statement:
--   The HDisc Lat construction uses the lattice main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAB.lean#L40-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAB.lean#L40-L196

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.HDiscLat
open Module
variable {R F : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F]
  [Algebra R F] [IsFractionRing R F]
  {ι : Type} [Fintype ι] [DecidableEq ι] {L : ι → Type} [∀ c, Field (L c)] [∀ c, Algebra F (L c)]
  [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)] [∀ c, Algebra R (L c)]
  [∀ c, IsScalarTower R F (L c)]

theorem ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.lattice_main {ϖ : R} (hϖ : Irreducible ϖ) (g : ∀ c, L c) (hg : ∀ c, g c ≠ 0)
    {m : ℕ} (hm : m = ∑ c, finrank F (L c)) (b : Fin m → ∀ c, L c)
    (hb : ∀ k c, g c * b k c ∈ integralClosure R (L c)) (hli : LinearIndependent F b) :
    ∃ n t : ℕ, ∃ u : Rˣ,
      Module.length R
        (↥(Submodule.span R {y : ∀ c, L c | ∀ c, g c * y c ∈ integralClosure R (L c)}) ⧸
          (Submodule.span R (Set.range b)).comap
            (Submodule.span R {y : ∀ c, L c | ∀ c, g c * y c ∈ integralClosure R (L c)}).subtype) = n ∧
      (Matrix.of fun k l : Fin m => ∑ c, Algebra.trace F (L c) (b k c * b l c)).det *
          (∏ c, Algebra.norm F (g c)) ^ 2 = algebraMap R F (↑u * ϖ ^ (2 * n + t)) := by sorry
