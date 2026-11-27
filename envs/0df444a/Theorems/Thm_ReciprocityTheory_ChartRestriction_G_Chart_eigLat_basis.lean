-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_eigLat_basis
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.eigLat_basis
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:20:22.903677+00:00
-- url     : https://prove2.me/theorems/9d57a071-0421-5d47-af06-3f39fb43e3f7
-- title:
--   Chart: eig Lat basis
-- statement:
--   The Chart construction uses the eig Lat basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/EigLatBasis.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/EigLatBasis.lean#L21-L24

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LieEig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)

theorem ReciprocityTheory.ChartRestriction.G.Chart.eigLat_basis [IsDomain R] [IsPrincipalIdealRing R] {O : Type} (act : O → (G ⟶ G)) [∀ a, IsMonHom (act a)]
    (χ : O → R) : ∃ k, Nonempty (Module.Basis (Fin k) R (eigLat hx act χ)) := by sorry
