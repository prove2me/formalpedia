-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_mem_ker_pieceMap
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.mem_ker_pieceMap
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:10:23.155657+00:00
-- url     : https://prove2.me/theorems/9ea9478a-2fcf-5d18-bc47-c2cc3ed25c5e
-- title:
--   Arakelov Geometry: mem ker piece Map
-- statement:
--   The Arakelov Geometry construction uses the mem ker piece Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/IsHomogeneousGrL.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/IsHomogeneousGrL.lean#L53-L55

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.mem_ker_pieceMap (J : Ideal (MRing ι)) (a : K → ℕ) (x : mHom ι a) :
    x ∈ LinearMap.ker (pieceMap J a) ↔ (x : MRing ι) ∈ J := by sorry
