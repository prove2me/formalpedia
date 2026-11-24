-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_fsum_sumElim
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.fsum_sumElim
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:28.747842+00:00
-- url     : https://prove2.me/theorems/703ab4ba-b41e-4334-b34e-39121c0ae086
-- title:
--   DVR: fsum sum Elim
-- statement:
--   The DVR construction uses the fsum sum Elim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBTransport.lean#L487-L489
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBTransport.lean#L487-L489

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped Classical
variable {X Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']

theorem ReciprocityTheory.ChartRestriction.G.DVR.fsum_sumElim {K₂ : Type} [Fintype K₂] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) :
    fsum (Sum.elim φ φ₂) (Sum.elim ε ε₂) = fsum φ ε + fsum φ₂ ε₂ := by sorry
