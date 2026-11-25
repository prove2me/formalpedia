-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_fsum_apply
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.fsum_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:11:12.449955+00:00
-- url     : https://prove2.me/theorems/50c7f949-05df-465f-bcab-85dc1a05314e
-- title:
--   DVR: fsum apply
-- statement:
--   The DVR construction uses the fsum apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBTransport.lean#L471-L473
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBTransport.lean#L471-L473

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.fsum_apply (φ : K → (Y ⟶ X)) (ε : K → ℤ) (ψ : Y ⟶ X) :
    fsum φ ε ψ = ∑ k, if φ k = ψ then ε k else 0 := by sorry
