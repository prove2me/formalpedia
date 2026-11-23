-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sec_compat_rs
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.sec_compat_rs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:25.554904+00:00
-- url     : https://prove2.me/theorems/c3f7957c-2224-4d8e-a7ad-5cacdd187709
-- title:
--   DVR: sec compat rs
-- statement:
--   The DVR construction uses the sec compat rs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBTransport.lean#L351-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBTransport.lean#L351-L363

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.sec_compat_rs (s : LB.Sec (LB.LinComb L φ ε)) (j j₂ : K → L.ι) {V : Y.Opens}
    (h : V ≤ LB.wchart L φ j ⊓ LB.wchart L φ j₂) :
    rs (h.trans inf_le_left) (s.f j) =
      ((∏ k, tr L V (φ k) (j k) (j₂ k) ^ ε k : Γ(Y, V)ˣ) : Γ(Y, V)) * rs (h.trans inf_le_right) (s.f j₂) := by sorry
