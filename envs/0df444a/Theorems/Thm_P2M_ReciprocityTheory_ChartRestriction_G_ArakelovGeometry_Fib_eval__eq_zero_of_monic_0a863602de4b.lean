-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_eval__eq_zero_of_monic_0a863602de4b
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_eval__eq_zero_of_monic_0a863602de4b
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:14:50.344637+00:00
-- url     : https://prove2.me/theorems/2c035f48-9580-5b77-8f7b-914227cb53cb
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Fib eval  eq zero of monic 0a863602de4b: P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Fib eval  eq zero of monic 0a863602
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Fib eval  eq zero of monic 0a863602de4b construction uses the P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Fib eval  eq zero of monic 0a863602de4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStA.lean#L121-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStA.lean#L121-L139

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_eval__eq_zero_of_monic_0a863602de4b {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* S) (ψ : R →+* T) (hker : ∀ m, φ m = 0 → ψ m = 0) {P : Polynomial R}
    (hP : P.Monic) {θ : S} {ρ : T}
    (hmin : ∀ H : Polynomial R, H.natDegree < P.natDegree → H.eval₂ φ θ = 0 →
      ∀ j, φ (H.coeff j) = 0)
    (hθ : P.eval₂ φ θ = 0) (hρ : P.eval₂ ψ ρ = 0) (hP1 : P ≠ 1) {H : Polynomial R}
    (hH : H.eval₂ φ θ = 0) : H.eval₂ ψ ρ = 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«ArakelovGeometry».«Fib».«eval₂_eq_zero_of_monic» := P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_eval__eq_zero_of_monic_0a863602de4b
