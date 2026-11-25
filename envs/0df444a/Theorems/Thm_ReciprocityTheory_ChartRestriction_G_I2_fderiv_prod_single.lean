-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_fderiv_prod_single
-- name    : ReciprocityTheory.ChartRestriction.G.I2.fderiv_prod_single
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:30:27.116152+00:00
-- url     : https://prove2.me/theorems/5a862947-3abf-548a-b71d-1daee119b8d2
-- title:
--   I2: fderiv prod single
-- statement:
--   The I2 construction uses the fderiv prod single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PolyDerivMonomialOne.lean#L47-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PolyDerivMonomialOne.lean#L47-L67

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

theorem ReciprocityTheory.ChartRestriction.G.I2.fderiv_prod_single {n : ℕ} {h : Fin n → W → ℂ} (hh : ∀ k, Differentiable ℂ (h k))
    (x : Fin n → W) (k0 : Fin n) (e : W) :
    fderiv ℂ (fun y : Fin n → W => ∏ k, h k (y k)) x (Pi.single k0 e) =
      (∏ k ∈ Finset.univ.erase k0, h k (x k)) * fderiv ℂ (h k0) (x k0) e := by sorry
