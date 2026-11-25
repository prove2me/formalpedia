-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_secScal_sval_c
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.secScal_sval_c
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:35:21.84322+00:00
-- url     : https://prove2.me/theorems/633c8113-18f1-46ea-9bf5-902982af672a
-- title:
--   DVR: sec Scal sval c
-- statement:
--   The DVR construction uses the sec Scal sval c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/NuExtA.lean#L105-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/NuExtA.lean#L105-L122

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThickKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_NuExtA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Out
variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]

theorem ReciprocityTheory.ChartRestriction.G.DVR.secScal_sval_c {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by sorry
