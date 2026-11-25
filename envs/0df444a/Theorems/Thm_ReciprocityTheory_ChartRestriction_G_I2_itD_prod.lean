-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_itD_prod
-- name    : ReciprocityTheory.ChartRestriction.G.I2.itD_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:16.152896+00:00
-- url     : https://prove2.me/theorems/b77fed37-1699-4c77-b646-564e657ab9e3
-- title:
--   I2: it D prod
-- statement:
--   The I2 construction uses the it D prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PolyDerivMonomialOne.lean#L77-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PolyDerivMonomialOne.lean#L77-L99

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
noncomputable section
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem ReciprocityTheory.ChartRestriction.G.I2.itD_prod {n : ℕ} {g : Fin n → W → ℂ} (hg : ∀ k, ContDiff ℂ (⊤ : ℕ∞) (g k))
    (L : List (Fin n × W)) (x : Fin n → W) :
    itD (fun v : Fin n → W => ∏ k, g k (v k)) (L.map fun p => Pi.single p.1 p.2) x =
      ∏ k, itD (g k) (colL L k) (x k) := by sorry
