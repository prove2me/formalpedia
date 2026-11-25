-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_sum_secFun_eq__d81f0b965cfc
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_sum_secFun_eq__d81f0b965cfc
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:01:03.096358+00:00
-- url     : https://prove2.me/theorems/96961865-5572-444a-8912-4f7289d46a76
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry sum sec Fun eq  d81f0b965cfc: P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry sum sec Fun eq  d81f0b965cfc
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry sum sec Fun eq  d81f0b965cfc construction uses the P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry sum sec Fun eq  d81f0b965cfc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStE.lean#L12-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStE.lean#L12-L33

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Matrix
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_sum_secFun_eq__d81f0b965cfc {x : Ix κ → Ω} {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : IsSecBasis x n b) (g : MvPolynomial (Ix κ) ℤ) (hg : g.IsHomogeneous n) (c : Fin r → ℤ)
    (hc : ∑ j, (c j : Ω) * aeval x (b j) = aeval x g) :
    ∀ z ∈ pts (coordIdeal ℤ x),
      ∑ j, (c j : ℂ) * secFun (b j) z = eval z (map (Int.castRingHom ℂ) g) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«ArakelovGeometry».«sum_secFun_eq'» := P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_sum_secFun_eq__d81f0b965cfc
