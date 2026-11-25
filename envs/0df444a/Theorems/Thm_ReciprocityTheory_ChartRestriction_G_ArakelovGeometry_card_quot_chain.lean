-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_card_quot_chain
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.card_quot_chain
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:04:34.952862+00:00
-- url     : https://prove2.me/theorems/3bec1e3e-50a7-4349-af0f-47f1b9491c1b
-- title:
--   Arakelov Geometry: card quot chain
-- statement:
--   The Arakelov Geometry construction uses the card quot chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/IsHomogeneousGrL.lean#L62-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/IsHomogeneousGrL.lean#L62-L77

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsPrimeFiltrationOfIsMultiHomogIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsHomogeneousGrL
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
attribute [local instance 2000] lexDecEq
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.card_quot_chain {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] (A B : Submodule R V)
    (h : A ≤ B) :
    Nat.card (V ⧸ A) = Nat.card (V ⧸ B) * Nat.card (B ⧸ A.comap B.subtype) := by sorry
