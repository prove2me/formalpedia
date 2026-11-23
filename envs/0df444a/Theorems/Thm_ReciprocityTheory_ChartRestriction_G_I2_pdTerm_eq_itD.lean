-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pdTerm_eq_itD
-- name    : ReciprocityTheory.ChartRestriction.G.I2.pdTerm_eq_itD
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:23.380993+00:00
-- url     : https://prove2.me/theorems/5fb089ed-21fb-4b41-a878-6c8b6da6d5fd
-- title:
--   I2: pd Term eq it D
-- statement:
--   The I2 construction uses the pd Term eq it D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PolyDerivMonomialOne.lean#L160-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PolyDerivMonomialOne.lean#L160-L169

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
variable {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem ReciprocityTheory.ChartRestriction.G.I2.pdTerm_eq_itD (u : σ → W) (F : W → ℂ) (x : W) (m : σ →₀ ℕ) :
    pdTerm u F x m = itD F ((Finsupp.toMultiset m).toList.map u) x := by sorry
