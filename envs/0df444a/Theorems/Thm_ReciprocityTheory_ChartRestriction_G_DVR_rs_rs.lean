-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_rs
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.rs_rs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:48.153816+00:00
-- url     : https://prove2.me/theorems/b2e93682-4ce0-4721-823d-ec5bf383b8bc
-- title:
--   DVR: rs rs
-- statement:
--   The DVR construction uses the rs rs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBTransport.lean#L314-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBTransport.lean#L314-L318

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.rs_rs {Z : Scheme.{0}} {U W V : Z.Opens} (h : W ≤ U) (h' : V ≤ W) (x : Γ(Z, U)) :
    rs h' (rs h x) = rs (h'.trans h) x := by sorry
