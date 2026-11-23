-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_div
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_div
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:38.233014+00:00
-- url     : https://prove2.me/theorems/f45e5bcc-854d-4b93-b17e-266b1e3325cb
-- title:
--   Tor: exists div
-- statement:
--   The Tor construction uses the exists div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DivCalc.lean#L203-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DivCalc.lean#L203-L274

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
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
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi
variable {V : Type} [CommRing V] {X Z : Scheme.{0}}

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_div [IsDomain V] (p : X ⟶ Sp V) [Flat p] {a : V} (ha : a ≠ 0) (W : X.Opens) (f : Γ(X, W))
    (h : ∀ x ∈ W, cst p x a ∣ gs (𝟙 X) x W f) : ∃ g : Γ(X, W), f = constFn p W a * g := by sorry
