-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_mul
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.rs_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:33:15.013077+00:00
-- url     : https://prove2.me/theorems/4e130b04-61c0-4a48-a1e8-e1a4e9b551a3
-- title:
--   DVR: rs mul
-- statement:
--   The DVR construction uses the rs mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBTransport.lean#L323-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBTransport.lean#L323-L324

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
variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}

theorem ReciprocityTheory.ChartRestriction.G.DVR.rs_mul {Z : Scheme.{0}} {U V : Z.Opens} (h : V ≤ U) (x y : Γ(Z, U)) :
    rs h (x * y) = rs h x * rs h y := by sorry
