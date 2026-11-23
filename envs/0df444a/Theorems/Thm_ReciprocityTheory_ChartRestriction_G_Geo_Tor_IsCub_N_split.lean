-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_split
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsCub.N_split
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:48:00.056086+00:00
-- url     : https://prove2.me/theorems/cb5fc37e-50bf-48ac-a292-38b131def71c
-- title:
--   Is Cub: N split
-- statement:
--   The Is Cub construction uses the N split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/CubeVal.lean#L49-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/CubeVal.lean#L49-L59

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
variable {A U : Type} [CommGroup A] [CommGroup U]
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsCub
variable {θ : A → A → A → U} (h : IsCub θ)
include h

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsCub.N_split (k : ℕ) (a m x : A) : cubN θ k a m x = θ a (m ^ k) x * cubN θ k 1 m x := by sorry
